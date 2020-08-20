/*********************                                                        */
/*! \file theory_model.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Clark Barrett, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of model class
 **/
#include "theory/theory_model.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {

TheoryModel::TheoryModel(context::Context* c,
                         std::string name,
                         bool enableFuncModels)
    : d_substitutions(c, false),
      d_modelBuilt(false),
      d_modelBuiltSuccess(false),
      d_using_model_core(false),
      d_enableFuncModels(enableFuncModels)
{
  // must use function models when ufHo is enabled
  Assert(d_enableFuncModels || !options::ufHo());
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );

  d_eeContext = new context::Context();
  d_equalityEngine = new eq::EqualityEngine(d_eeContext, name, false);

  // The kinds we are treating as function application in congruence
  d_equalityEngine->addFunctionKind(kind::APPLY_UF, false, options::ufHo());
  d_equalityEngine->addFunctionKind(kind::HO_APPLY);
  d_equalityEngine->addFunctionKind(kind::SELECT);
  // d_equalityEngine->addFunctionKind(kind::STORE);
  d_equalityEngine->addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine->addFunctionKind(kind::APPLY_SELECTOR_TOTAL);
  d_equalityEngine->addFunctionKind(kind::APPLY_TESTER);
  d_eeContext->push();
  // do not interpret APPLY_UF if we are not assigning function values
  if (!enableFuncModels)
  {
    setSemiEvaluatedKind(kind::APPLY_UF);
  }
}

TheoryModel::~TheoryModel()
{
  d_eeContext->pop();
  delete d_equalityEngine;
  delete d_eeContext;
}

void TheoryModel::reset(){
  d_modelBuilt = false;
  d_modelBuiltSuccess = false;
  d_modelCache.clear();
  d_comment_str.clear();
  d_sep_heap = Node::null();
  d_sep_nil_eq = Node::null();
  d_approximations.clear();
  d_approx_list.clear();
  d_reps.clear();
  d_assignExcSet.clear();
  d_aesMaster.clear();
  d_aesSlaves.clear();
  d_rep_set.clear();
  d_uf_terms.clear();
  d_ho_uf_terms.clear();
  d_uf_models.clear();
  d_eeContext->pop();
  d_eeContext->push();
  d_using_model_core = false;
  d_model_core.clear();
}

void TheoryModel::getComments(std::ostream& out) const {
  Trace("model-builder") << "get comments..." << std::endl;
  out << d_comment_str.str();
}

void TheoryModel::setHeapModel( Node h, Node neq ) { 
  d_sep_heap = h;
  d_sep_nil_eq = neq;
}

bool TheoryModel::getHeapModel( Expr& h, Expr& neq ) const {
  if( d_sep_heap.isNull() || d_sep_nil_eq.isNull() ){
    return false;
  }else{
    h = d_sep_heap.toExpr();
    neq = d_sep_nil_eq.toExpr();
    return true;
  }
}

bool TheoryModel::hasApproximations() const { return !d_approx_list.empty(); }

std::vector<std::pair<Expr, Expr> > TheoryModel::getApproximations() const
{
  std::vector<std::pair<Expr, Expr> > approx;
  for (const std::pair<Node, Node>& ap : d_approx_list)
  {
    approx.push_back(
        std::pair<Expr, Expr>(ap.first.toExpr(), ap.second.toExpr()));
  }
  return approx;
}

std::vector<Expr> TheoryModel::getDomainElements(Type t) const
{
  // must be an uninterpreted sort
  Assert(t.isSort());
  std::vector<Expr> elements;
  TypeNode tn = TypeNode::fromType(t);
  const std::vector<Node>* type_refs = d_rep_set.getTypeRepsOrNull(tn);
  if (type_refs == nullptr || type_refs->empty())
  {
    // This is called when t is a sort that does not occur in this model.
    // Sorts are always interpreted as non-empty, thus we add a single element.
    elements.push_back(t.mkGroundTerm());
    return elements;
  }
  for (const Node& n : *type_refs)
  {
    elements.push_back(n.toExpr());
  }
  return elements;
}

Node TheoryModel::getValue(TNode n) const
{
  //apply substitutions
  Node nn = d_substitutions.apply(n);
  Debug("model-getvalue-debug") << "[model-getvalue] getValue : substitute " << n << " to " << nn << std::endl;
  //get value in model
  nn = getModelValue(nn);
  if (nn.isNull()) return nn;
  if(options::condenseFunctionValues() || nn.getKind() != kind::LAMBDA) {
    //normalize
    nn = Rewriter::rewrite(nn);
  }
  Debug("model-getvalue") << "[model-getvalue] getValue( " << n << " ): " << std::endl
                          << "[model-getvalue] returning " << nn << std::endl;
  return nn;
}

bool TheoryModel::isModelCoreSymbol(Expr sym) const
{
  if (!d_using_model_core)
  {
    return true;
  }
  Node s = Node::fromExpr(sym);
  Assert(s.isVar() && s.getKind() != BOUND_VARIABLE);
  return d_model_core.find(s) != d_model_core.end();
}

Expr TheoryModel::getValue( Expr expr ) const{
  Node n = Node::fromExpr( expr );
  Node ret = getValue( n );
  return ret.toExpr();
}

/** get cardinality for sort */
Cardinality TheoryModel::getCardinality( Type t ) const{
  TypeNode tn = TypeNode::fromType( t );
  //for now, we only handle cardinalities for uninterpreted sorts
  if( tn.isSort() ){
    if( d_rep_set.hasType( tn ) ){
      Debug("model-getvalue-debug") << "Get cardinality sort, #rep : " << d_rep_set.getNumRepresentatives( tn ) << std::endl;
      return Cardinality( d_rep_set.getNumRepresentatives( tn ) );
    }else{
      Debug("model-getvalue-debug") << "Get cardinality sort, unconstrained, return 1." << std::endl;
      return Cardinality( 1 );
    }
  }else{
      Debug("model-getvalue-debug") << "Get cardinality other sort, unknown." << std::endl;
    return Cardinality( CardinalityUnknown() );
  }
}

Node TheoryModel::getModelValue(TNode n) const
{
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it = d_modelCache.find(n);
  if (it != d_modelCache.end()) {
    return (*it).second;
  }
  Debug("model-getvalue-debug") << "Get model value " << n << " ... ";
  Debug("model-getvalue-debug") << d_equalityEngine->hasTerm(n) << std::endl;
  Kind nk = n.getKind();
  if (n.isConst() || nk == BOUND_VARIABLE)
  {
    d_modelCache[n] = n;
    return n;
  }

  Node ret = n;
  NodeManager* nm = NodeManager::currentNM();

  // if it is an evaluated kind, compute model values for children and evaluate
  if (n.getNumChildren() > 0
      && d_unevaluated_kinds.find(nk) == d_unevaluated_kinds.end()
      && d_semi_evaluated_kinds.find(nk) == d_semi_evaluated_kinds.end())
  {
    Debug("model-getvalue-debug")
        << "Get model value children " << n << std::endl;
    std::vector<Node> children;
    if (n.getKind() == APPLY_UF)
    {
      Node op = getModelValue(n.getOperator());
      Debug("model-getvalue-debug") << "  operator : " << op << std::endl;
      children.push_back(op);
    }
    else if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    // evaluate the children
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; ++i)
    {
      ret = getModelValue(n[i]);
      Debug("model-getvalue-debug")
          << "  " << n << "[" << i << "] is " << ret << std::endl;
      children.push_back(ret);
    }
    ret = nm->mkNode(n.getKind(), children);
    Debug("model-getvalue-debug") << "ret (pre-rewrite): " << ret << std::endl;
    ret = Rewriter::rewrite(ret);
    Debug("model-getvalue-debug") << "ret (post-rewrite): " << ret << std::endl;
    // special cases
    if (ret.getKind() == kind::CARDINALITY_CONSTRAINT)
    {
      Debug("model-getvalue-debug")
          << "get cardinality constraint " << ret[0].getType() << std::endl;
      ret = nm->mkConst(
          getCardinality(ret[0].getType().toType()).getFiniteCardinality()
          <= ret[1].getConst<Rational>().getNumerator());
    }
    else if (ret.getKind() == kind::CARDINALITY_VALUE)
    {
      Debug("model-getvalue-debug")
          << "get cardinality value " << ret[0].getType() << std::endl;
      ret = nm->mkConst(Rational(
          getCardinality(ret[0].getType().toType()).getFiniteCardinality()));
    }
    d_modelCache[n] = ret;
    return ret;
  }
  // it might be approximate
  std::map<Node, Node>::const_iterator ita = d_approximations.find(n);
  if (ita != d_approximations.end())
  {
    // If the value of n is approximate based on predicate P(n), we return
    // witness z. P(z).
    Node v = nm->mkBoundVar(n.getType());
    Node bvl = nm->mkNode(BOUND_VAR_LIST, v);
    Node answer = nm->mkNode(WITNESS, bvl, ita->second.substitute(n, v));
    d_modelCache[n] = answer;
    return answer;
  }
  // must rewrite the term at this point
  ret = Rewriter::rewrite(n);
  // return the representative of the term in the equality engine, if it exists
  TypeNode t = ret.getType();
  bool eeHasTerm;
  if (!options::ufHo() && (t.isFunction() || t.isPredicate()))
  {
    // functions are in the equality engine, but *not* as first-class members
    // when higher-order is disabled. In this case, we cannot query
    // representatives for functions since they are "internal" nodes according
    // to the equality engine despite hasTerm returning true. However, they are
    // first class members when higher-order is enabled. Hence, the special
    // case here.
    eeHasTerm = false;
  }
  else
  {
    eeHasTerm = d_equalityEngine->hasTerm(ret);
  }
  if (eeHasTerm)
  {
    Debug("model-getvalue-debug")
        << "get value from representative " << ret << "..." << std::endl;
    ret = d_equalityEngine->getRepresentative(ret);
    Assert(d_reps.find(ret) != d_reps.end());
    std::map<Node, Node>::const_iterator it2 = d_reps.find(ret);
    if (it2 != d_reps.end())
    {
      ret = it2->second;
      d_modelCache[n] = ret;
      return ret;
    }
  }

  // if we are a evaluated or semi-evaluated kind, return an arbitrary value
  // if we are not in the d_unevaluated_kinds map, we are evaluated
  if (d_unevaluated_kinds.find(nk) == d_unevaluated_kinds.end())
  {
    if (t.isFunction() || t.isPredicate())
    {
      if (d_enableFuncModels)
      {
        std::map<Node, Node>::const_iterator entry = d_uf_models.find(n);
        if (entry != d_uf_models.end())
        {
          // Existing function
          ret = entry->second;
          d_modelCache[n] = ret;
          return ret;
        }
        // Unknown function symbol: return LAMBDA x. c, where c is the first
        // constant in the enumeration of the range type
        vector<TypeNode> argTypes = t.getArgTypes();
        vector<Node> args;
        for (unsigned i = 0, size = argTypes.size(); i < size; ++i)
        {
          args.push_back(nm->mkBoundVar(argTypes[i]));
        }
        Node boundVarList = nm->mkNode(kind::BOUND_VAR_LIST, args);
        TypeEnumerator te(t.getRangeType());
        ret = nm->mkNode(kind::LAMBDA, boundVarList, *te);
      }
      else
      {
        // if func models not enabled, throw an error
        Unreachable();
      }
    }
    else if (!t.isFirstClass())
    {
      // this is the class for regular expressions
      // we simply invoke the rewriter on them
      ret = Rewriter::rewrite(ret);
    }
    else
    {
      // Unknown term - return first enumerated value for this type
      TypeEnumerator te(n.getType());
      ret = *te;
    }
    d_modelCache[n] = ret;
    return ret;
  }

  d_modelCache[n] = n;
  return n;
}

/** add substitution */
void TheoryModel::addSubstitution( TNode x, TNode t, bool invalidateCache ){
  if( !d_substitutions.hasSubstitution( x ) ){
    Debug("model") << "Add substitution in model " << x << " -> " << t << std::endl;
    d_substitutions.addSubstitution( x, t, invalidateCache );
  } else {
#ifdef CVC4_ASSERTIONS
    Node oldX = d_substitutions.getSubstitution(x);
    // check that either the old substitution is the same, or it now maps to the new substitution
    if(oldX != t && d_substitutions.apply(oldX) != d_substitutions.apply(t)) {
      InternalError()
          << "Two incompatible substitutions added to TheoryModel:\n"
          << "the term:    " << x << "\n"
          << "old mapping: " << d_substitutions.apply(oldX) << "\n"
          << "new mapping: " << d_substitutions.apply(t);
    }
#endif /* CVC4_ASSERTIONS */
  }
}

/** add term */
void TheoryModel::addTermInternal(TNode n)
{
  Assert(d_equalityEngine->hasTerm(n));
  Trace("model-builder-debug2") << "TheoryModel::addTerm : " << n << std::endl;
  //must collect UF terms
  if (n.getKind()==APPLY_UF) {
    Node op = n.getOperator();
    if( std::find( d_uf_terms[ op ].begin(), d_uf_terms[ op ].end(), n )==d_uf_terms[ op ].end() ){
      d_uf_terms[ op ].push_back( n );
      Trace("model-builder-fun") << "Add apply term " << n << std::endl;
    }
  }else if( n.getKind()==HO_APPLY ){
    Node op = n[0];
    if( std::find( d_ho_uf_terms[ op ].begin(), d_ho_uf_terms[ op ].end(), n )==d_ho_uf_terms[ op ].end() ){
      d_ho_uf_terms[ op ].push_back( n );
      Trace("model-builder-fun") << "Add ho apply term " << n << std::endl;
    }
  }
  // all functions must be included, marked as higher-order
  if( n.getType().isFunction() ){
    Trace("model-builder-fun") << "Add function variable (without term) " << n << std::endl;
    if( d_uf_terms.find( n )==d_uf_terms.end() ){
      d_uf_terms[n].clear();
    }
    if( d_ho_uf_terms.find( n )==d_ho_uf_terms.end() ){
      d_ho_uf_terms[n].clear();
    }
  }
}

/** assert equality */
bool TheoryModel::assertEquality(TNode a, TNode b, bool polarity)
{
  Assert(d_equalityEngine->consistent());
  if (a == b && polarity) {
    return true;
  }
  Trace("model-builder-assertions") << "(assert " << (polarity ? "(= " : "(not (= ") << a << " " << b << (polarity ? "));" : ")));") << endl;
  d_equalityEngine->assertEquality( a.eqNode(b), polarity, Node::null() );
  return d_equalityEngine->consistent();
}

/** assert predicate */
bool TheoryModel::assertPredicate(TNode a, bool polarity)
{
  Assert(d_equalityEngine->consistent());
  if ((a == d_true && polarity) ||
      (a == d_false && (!polarity))) {
    return true;
  }
  if (a.getKind() == EQUAL) {
    Trace("model-builder-assertions") << "(assert " << (polarity ? " " : "(not ") << a << (polarity ? ");" : "));") << endl;
    d_equalityEngine->assertEquality( a, polarity, Node::null() );
  } else {
    Trace("model-builder-assertions") << "(assert " << (polarity ? "" : "(not ") << a << (polarity ? ");" : "));") << endl;
    d_equalityEngine->assertPredicate( a, polarity, Node::null() );
  }
  return d_equalityEngine->consistent();
}

/** assert equality engine */
bool TheoryModel::assertEqualityEngine(const eq::EqualityEngine* ee,
                                       set<Node>* termSet)
{
  Assert(d_equalityEngine->consistent());
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  for (; !eqcs_i.isFinished(); ++eqcs_i) {
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predTrue = false;
    bool predFalse = false;
    Trace("model-builder-debug") << "...asserting terms in equivalence class " << eqc;
    if (eqc.getType().isBoolean()) {
      predicate = true;
      predTrue = ee->areEqual(eqc, d_true);
      predFalse = ee->areEqual(eqc, d_false);
      Trace("model-builder-debug") << ", pred = " << predTrue << "/" << predFalse;
    }
    Trace("model-builder-debug") << std::endl;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
    bool first = true;
    Node rep;
    for (; !eqc_i.isFinished(); ++eqc_i) {
      if (termSet != NULL && termSet->find(*eqc_i) == termSet->end()) {
        Trace("model-builder-debug") << "...skip node " << (*eqc_i) << " in eqc " << eqc << std::endl;
        continue;
      }
      if (predicate) {
        if (predTrue || predFalse)
        {
          if (!assertPredicate(*eqc_i, predTrue))
          {
            return false;
          }
        }
        else {
          if (first) {
            rep = (*eqc_i);
            first = false;
          }
          else {
            Node eq = (*eqc_i).eqNode(rep);
            Trace("model-builder-assertions")
                << "(assert " << eq << ");" << std::endl;
            d_equalityEngine->assertEquality(eq, true, Node::null());
            if (!d_equalityEngine->consistent())
            {
              return false;
            }
          }
        }
      } else {
        if (first) {
          rep = (*eqc_i);
          //add the term (this is specifically for the case of singleton equivalence classes)
          if (rep.getType().isFirstClass())
          {
            d_equalityEngine->addTerm( rep );
            Trace("model-builder-debug") << "Add term to ee within assertEqualityEngine: " << rep << std::endl;
          }
          first = false;
        }
        else {
          if (!assertEquality(*eqc_i, rep, true))
          {
            return false;
          }
        }
      }
    }
  }
  return true;
}

void TheoryModel::assertSkeleton(TNode n)
{
  Trace("model-builder-reps") << "Assert skeleton : " << n << std::endl;
  Trace("model-builder-reps") << "...rep eqc is : " << getRepresentative(n)
                              << std::endl;
  d_reps[ n ] = n;
}

void TheoryModel::setAssignmentExclusionSet(TNode n,
                                            const std::vector<Node>& eset)
{
  // should not be assigned yet
  Assert(d_assignExcSet.find(n) == d_assignExcSet.end());
  Trace("model-builder-debug")
      << "Exclude values of " << n << " : " << eset << std::endl;
  std::vector<Node>& aes = d_assignExcSet[n];
  aes.insert(aes.end(), eset.begin(), eset.end());
}

void TheoryModel::setAssignmentExclusionSetGroup(
    const std::vector<TNode>& group, const std::vector<Node>& eset)
{
  if (group.empty())
  {
    return;
  }
  // for efficiency, we store a single copy of eset and set a slave/master
  // relationship
  setAssignmentExclusionSet(group[0], eset);
  std::vector<Node>& gslaves = d_aesSlaves[group[0]];
  for (unsigned i = 1, gsize = group.size(); i < gsize; ++i)
  {
    Node gs = group[i];
    // set master
    d_aesMaster[gs] = group[0];
    // add to slaves
    gslaves.push_back(gs);
  }
}

bool TheoryModel::getAssignmentExclusionSet(TNode n,
                                            std::vector<Node>& group,
                                            std::vector<Node>& eset)
{
  // does it have a master?
  std::map<Node, Node>::iterator itm = d_aesMaster.find(n);
  if (itm != d_aesMaster.end())
  {
    return getAssignmentExclusionSet(itm->second, group, eset);
  }
  std::map<Node, std::vector<Node> >::iterator ita = d_assignExcSet.find(n);
  if (ita == d_assignExcSet.end())
  {
    return false;
  }
  eset.insert(eset.end(), ita->second.begin(), ita->second.end());
  group.push_back(n);
  // does it have slaves?
  ita = d_aesSlaves.find(n);
  if (ita != d_aesSlaves.end())
  {
    group.insert(group.end(), ita->second.begin(), ita->second.end());
  }
  return true;
}

bool TheoryModel::hasAssignmentExclusionSets() const
{
  return !d_assignExcSet.empty();
}

void TheoryModel::recordApproximation(TNode n, TNode pred)
{
  Trace("model-builder-debug")
      << "Record approximation : " << n << " satisfies the predicate " << pred
      << std::endl;
  Assert(d_approximations.find(n) == d_approximations.end());
  Assert(pred.getType().isBoolean());
  d_approximations[n] = pred;
  d_approx_list.push_back(std::pair<Node, Node>(n, pred));
  // model cache is invalid
  d_modelCache.clear();
}
void TheoryModel::recordApproximation(TNode n, TNode pred, Node witness)
{
  Node predDisj = NodeManager::currentNM()->mkNode(OR, n.eqNode(witness), pred);
  recordApproximation(n, predDisj);
}
void TheoryModel::setUsingModelCore()
{
  d_using_model_core = true;
  d_model_core.clear();
}

void TheoryModel::recordModelCoreSymbol(Expr sym)
{
  d_model_core.insert(Node::fromExpr(sym));
}

void TheoryModel::setUnevaluatedKind(Kind k) { d_unevaluated_kinds.insert(k); }

void TheoryModel::setSemiEvaluatedKind(Kind k)
{
  d_semi_evaluated_kinds.insert(k);
}

bool TheoryModel::isLegalElimination(TNode x, TNode val)
{
  return !expr::hasSubtermKinds(d_unevaluated_kinds, val);
}

bool TheoryModel::hasTerm(TNode a)
{
  return d_equalityEngine->hasTerm( a );
}

Node TheoryModel::getRepresentative(TNode a)
{
  if( d_equalityEngine->hasTerm( a ) ){
    Node r = d_equalityEngine->getRepresentative( a );
    if( d_reps.find( r )!=d_reps.end() ){
      return d_reps[ r ];
    }else{
      return r;
    }
  }else{
    return a;
  }
}

bool TheoryModel::areEqual(TNode a, TNode b)
{
  if( a==b ){
    return true;
  }else if( d_equalityEngine->hasTerm( a ) && d_equalityEngine->hasTerm( b ) ){
    return d_equalityEngine->areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryModel::areDisequal(TNode a, TNode b)
{
  if( d_equalityEngine->hasTerm( a ) && d_equalityEngine->hasTerm( b ) ){
    return d_equalityEngine->areDisequal( a, b, false );
  }else{
    return false;
  }
}

bool TheoryModel::areFunctionValuesEnabled() const
{
  return d_enableFuncModels;
}

void TheoryModel::assignFunctionDefinition( Node f, Node f_def ) {
  Trace("model-builder") << "  Assigning function (" << f << ") to (" << f_def << ")" << endl;
  Assert(d_uf_models.find(f) == d_uf_models.end());

  if( options::ufHo() ){
    //we must rewrite the function value since the definition needs to be a constant value
    f_def = Rewriter::rewrite( f_def );
    Trace("model-builder-debug")
        << "Model value (post-rewrite) : " << f_def << std::endl;
    Assert(f_def.isConst()) << "Non-constant f_def: " << f_def;
  }
 
  // d_uf_models only stores models for variables
  if( f.isVar() ){
    d_uf_models[f] = f_def;
  }

  if (options::ufHo() && d_equalityEngine->hasTerm(f))
  {
    Trace("model-builder-debug") << "  ...function is first-class member of equality engine" << std::endl;
    // assign to representative if higher-order
    Node r = d_equalityEngine->getRepresentative( f );
    //always replace the representative, since it is initially assigned to itself
    Trace("model-builder") << "    Assign: Setting function rep " << r << " to " << f_def << endl;
    d_reps[r] = f_def;  
    // also assign to other assignable functions in the same equivalence class
    eq::EqClassIterator eqc_i = eq::EqClassIterator(r,d_equalityEngine);
    while( !eqc_i.isFinished() ) {
      Node n = *eqc_i;
      // if an unassigned variable function
      if( n.isVar() && d_uf_terms.find( n )!=d_uf_terms.end() && !hasAssignedFunctionDefinition( n ) ){
        d_uf_models[n] = f_def;
        Trace("model-builder") << "  Assigning function (" << n << ") to function definition of " << f << std::endl;
      }
      ++eqc_i;
    }
    Trace("model-builder-debug") << "  ...finished." << std::endl;
  }
}

std::vector< Node > TheoryModel::getFunctionsToAssign() {
  std::vector< Node > funcs_to_assign;
  std::map< Node, Node > func_to_rep;

  // collect functions
  for( std::map< Node, std::vector< Node > >::iterator it = d_uf_terms.begin(); it != d_uf_terms.end(); ++it ){
    Node n = it->first;
    Assert(!n.isNull());
    if( !hasAssignedFunctionDefinition( n ) ){
      Trace("model-builder-fun-debug") << "Look at function : " << n << std::endl;
      if( options::ufHo() ){
        // if in higher-order mode, assign function definitions modulo equality
        Node r = getRepresentative( n );
        std::map< Node, Node >::iterator itf = func_to_rep.find( r );
        if( itf==func_to_rep.end() ){
          func_to_rep[r] = n;
          funcs_to_assign.push_back( n );
          Trace("model-builder-fun") << "Make function " << n;
          Trace("model-builder-fun") << " the assignable function in its equivalence class." << std::endl;
        }else{
          // must combine uf terms          
          Trace("model-builder-fun") << "Copy " << it->second.size() << " uf terms";
          d_uf_terms[itf->second].insert( d_uf_terms[itf->second].end(), it->second.begin(), it->second.end() );
          std::map< Node, std::vector< Node > >::iterator ith = d_ho_uf_terms.find( n );
          if( ith!=d_ho_uf_terms.end() ){
            d_ho_uf_terms[itf->second].insert( d_ho_uf_terms[itf->second].end(), ith->second.begin(), ith->second.end() );
            Trace("model-builder-fun") << " and " << ith->second.size() << " ho uf terms";
          }
          Trace("model-builder-fun") << " from " << n << " to its assignable representative function " << itf->second << std::endl;
          it->second.clear();
        }
      }else{
        Trace("model-builder-fun") << "Function to assign : " << n << std::endl;
        funcs_to_assign.push_back( n );
      }
    }
  }

  Trace("model-builder-fun") << "return " << funcs_to_assign.size() << " functions to assign..." << std::endl;
  return funcs_to_assign;
}

} /* namespace CVC4::theory */
} /* namespace CVC4 */
