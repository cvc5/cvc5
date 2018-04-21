/*********************                                                        */
/*! \file theory_model.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of model class
 **/
#include "theory/theory_model.h"

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
      d_enableFuncModels(enableFuncModels)
{
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
  d_reps.clear();
  d_rep_set.clear();
  d_uf_terms.clear();
  d_ho_uf_terms.clear();
  d_uf_models.clear();
  d_eeContext->pop();
  d_eeContext->push();
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

Node TheoryModel::getValue(TNode n, bool useDontCares) const {
  //apply substitutions
  Node nn = d_substitutions.apply(n);
  Debug("model-getvalue-debug") << "[model-getvalue] getValue : substitute " << n << " to " << nn << std::endl;
  //get value in model
  nn = getModelValue(nn, false, useDontCares);
  if (nn.isNull()) return nn;
  if(options::condenseFunctionValues() || nn.getKind() != kind::LAMBDA) {
    //normalize
    nn = Rewriter::rewrite(nn);
  }
  Debug("model-getvalue") << "[model-getvalue] getValue( " << n << " ): " << std::endl
                          << "[model-getvalue] returning " << nn << std::endl;
  return nn;
}

bool TheoryModel::isDontCare(Expr expr) const {
  return getValue(Node::fromExpr(expr), true).isNull();
}

Expr TheoryModel::getValue( Expr expr ) const{
  Node n = Node::fromExpr( expr );
  Node ret = getValue( n );
  return d_smt.postprocess(ret, TypeNode::fromType(expr.getType())).toExpr();
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

Node TheoryModel::getModelValue(TNode n, bool hasBoundVars, bool useDontCares) const
{
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it = d_modelCache.find(n);
  if (it != d_modelCache.end()) {
    return (*it).second;
  }
  Debug("model-getvalue-debug") << "Get model value " << n << " ... ";
  Debug("model-getvalue-debug") << d_equalityEngine->hasTerm(n) << std::endl;
  Node ret = n;
  if(n.getKind() == kind::EXISTS || n.getKind() == kind::FORALL || n.getKind() == kind::COMBINED_CARDINALITY_CONSTRAINT ) {
    // We should have terms, thanks to TheoryQuantifiers::collectModelInfo().
    // However, if the Decision Engine stops us early, there might be a
    // quantifier that isn't assigned.  In conjunction with miniscoping, this
    // might lead to a perfectly good model.  Think of
    //     ASSERT FORALL(x) : p OR x=5
    // The p is pulled out by miniscoping, and set to TRUE by the decision
    // engine, then the quantifier's value in the model doesn't matter, so the
    // Decision Engine stops.  So even though the top-level quantifier was
    // asserted, it can't be checked directly: first, it doesn't "exist" in
    // non-miniscoped form, and second, no quantifiers have been asserted, so
    // none is in the model.  We used to fail an assertion here, but that's
    // no good.  Instead, return the quantifier itself.  If we're in
    // checkModel(), and the quantifier actually matters, we'll get an
    // assert-fail since the quantifier isn't a constant.
    Node nr = Rewriter::rewrite(n);
    if(!d_equalityEngine->hasTerm(nr)) {
      d_modelCache[n] = ret;
      return ret;
    } else {
      ret = nr;
    }
  } else {
    // FIXME : special case not necessary? (also address BV_ACKERMANIZE functions below), github issue #1116
    if(n.getKind() == kind::LAMBDA) {
      NodeManager* nm = NodeManager::currentNM();
      Node body = getModelValue(n[1], true);
      body = Rewriter::rewrite(body);
      ret = nm->mkNode(kind::LAMBDA, n[0], body);
      ret = Rewriter::rewrite( ret );
      d_modelCache[n] = ret;
      return ret;
    }
    if(n.isConst() || (hasBoundVars && n.getKind() == kind::BOUND_VARIABLE)) {
      d_modelCache[n] = ret;
      return ret;
    }
  
    if (n.getNumChildren() > 0 &&
        n.getKind() != kind::BITVECTOR_ACKERMANIZE_UDIV &&
        n.getKind() != kind::BITVECTOR_ACKERMANIZE_UREM) {
      Debug("model-getvalue-debug") << "Get model value children " << n << std::endl;
      std::vector<Node> children;
      if (n.getKind() == APPLY_UF) {
        Node op = getModelValue(n.getOperator(), hasBoundVars);
        Debug("model-getvalue-debug") << "  operator : " << op << std::endl;
        children.push_back(op);
      }
      else if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(n.getOperator());
      }
      //evaluate the children
      for (unsigned i = 0; i < n.getNumChildren(); ++i) {
        ret = getModelValue(n[i], hasBoundVars);
        Debug("model-getvalue-debug") << "  " << n << "[" << i << "] is " << ret << std::endl;
        children.push_back(ret);
      }
      ret = NodeManager::currentNM()->mkNode(n.getKind(), children);
      Debug("model-getvalue-debug") << "ret (pre-rewrite): " << ret << std::endl;
      ret = Rewriter::rewrite(ret);
      Debug("model-getvalue-debug") << "ret (post-rewrite): " << ret << std::endl;
      if(ret.getKind() == kind::CARDINALITY_CONSTRAINT) {
        Debug("model-getvalue-debug") << "get cardinality constraint " << ret[0].getType() << std::endl;
        ret = NodeManager::currentNM()->mkConst(getCardinality(ret[0].getType().toType()).getFiniteCardinality() <= ret[1].getConst<Rational>().getNumerator());
      }else if(ret.getKind() == kind::CARDINALITY_VALUE) {
        Debug("model-getvalue-debug") << "get cardinality value " << ret[0].getType() << std::endl;
        ret = NodeManager::currentNM()->mkConst(Rational(getCardinality(ret[0].getType().toType()).getFiniteCardinality()));
      }
      d_modelCache[n] = ret;
      return ret;
    }
  
    Debug("model-getvalue-debug") << "Handling special cases for types..." << std::endl;
    TypeNode t = n.getType();
    bool eeHasTerm;
    if( !options::ufHo() && (t.isFunction() || t.isPredicate()) ){
      // functions are in the equality engine, but *not* as first-class members
      // when higher-order is disabled. In this case, we cannot query representatives for functions
      // since they are "internal" nodes according to the equality engine despite hasTerm returning true. 
      // However, they are first class members when higher-order is enabled. Hence, the special
      // case here.
      eeHasTerm = false;
    }else{
      eeHasTerm = d_equalityEngine->hasTerm(n);
    }
    // if the term does not exist in the equality engine, return an arbitrary value
    if (!eeHasTerm) {
      if (t.isFunction() || t.isPredicate()) {
        if (d_enableFuncModels) {
          std::map< Node, Node >::const_iterator it = d_uf_models.find(n);
          if (it != d_uf_models.end()) {
            // Existing function
            ret = it->second;
            d_modelCache[n] = ret;
            return ret;
          }
          // Unknown function symbol: return LAMBDA x. c, where c is the first constant in the enumeration of the range type
          vector<TypeNode> argTypes = t.getArgTypes();
          vector<Node> args;
          NodeManager* nm = NodeManager::currentNM();
          for (unsigned i = 0; i < argTypes.size(); ++i) {
            args.push_back(nm->mkBoundVar(argTypes[i]));
          }
          Node boundVarList = nm->mkNode(kind::BOUND_VAR_LIST, args);
          TypeEnumerator te(t.getRangeType());
          ret = nm->mkNode(kind::LAMBDA, boundVarList, *te);
        }else{
          // TODO: if func models not enabled, throw an error?
          Unreachable();
        }
      }
      else if (!t.isFirstClass())
      {
        // this is the class for regular expressions
        // we simply invoke the rewriter on them
        ret = Rewriter::rewrite(ret);
      } else {
        if (options::omitDontCares() && useDontCares) {
          return Node();
        }
        // Unknown term - return first enumerated value for this type
        TypeEnumerator te(n.getType());
        ret = *te;
      }
      d_modelCache[n] = ret;
      return ret;
    }
  }
  Debug("model-getvalue-debug") << "get value from representative " << ret << "..." << std::endl;
  ret = d_equalityEngine->getRepresentative(ret);
  Assert(d_reps.find(ret) != d_reps.end());
  std::map< Node, Node >::const_iterator it2 = d_reps.find( ret );
  if (it2 != d_reps.end()) {
    ret = it2->second;
  } else {
    ret = Node::null();
  }
  d_modelCache[n] = ret;
  return ret;
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
      stringstream ss;
      ss << "Two incompatible substitutions added to TheoryModel:\n"
         << "the term:    " << x << "\n"
         << "old mapping: " << d_substitutions.apply(oldX) << "\n"
         << "new mapping: " << d_substitutions.apply(t);
      InternalError(ss.str());
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
            Trace("model-builder-assertions") << "(assert (= " << *eqc_i << " " << rep << "));" << endl;
            d_equalityEngine->mergePredicates(*eqc_i, rep, Node::null());
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

//for debugging
void TheoryModel::printRepresentativeDebug( const char* c, Node r ){
  if( r.isNull() ){
    Trace( c ) << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      Trace( c ) << "true";
    }else{
      Trace( c ) << "false";
    }
  }else{
    Trace( c ) << getRepresentative( r );
  }
}

void TheoryModel::printRepresentative( std::ostream& out, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    out << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      out  << "true";
    }else{
      out  << "false";
    }
  }else{
    out << getRepresentative( r );
  }
}

void TheoryModel::assignFunctionDefinition( Node f, Node f_def ) {
  Assert( d_uf_models.find( f )==d_uf_models.end() );
  Trace("model-builder") << "  Assigning function (" << f << ") to (" << f_def << ")" << endl;

  if( options::ufHo() ){
    //we must rewrite the function value since the definition needs to be a constant value
    f_def = Rewriter::rewrite( f_def );
    Assert( f_def.isConst() );
  }
 
  // d_uf_models only stores models for variables
  if( f.isVar() ){
    d_uf_models[f] = f_def;
  }

  if( options::ufHo() ){
    Trace("model-builder-debug") << "  ...function is first-class member of equality engine" << std::endl;
    Assert(d_equalityEngine->hasTerm(f));
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
    Assert( !n.isNull() );
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
