/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This is the interface to TheoryUF implementations
 *
 * All implementations of TheoryUF should inherit from this class.
 */

#include "theory/uf/theory_uf.h"

#include <memory>
#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "proof/proof_node_manager.h"
#include "smt/logic_exception.h"
#include "theory/theory_model.h"
#include "theory/type_enumerator.h"
#include "theory/uf/cardinality_extension.h"
#include "theory/uf/ho_extension.h"
#include "theory/uf/lambda_lift.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace std;

namespace cvc5 {
namespace theory {
namespace uf {

/** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
TheoryUF::TheoryUF(Env& env,
                   OutputChannel& out,
                   Valuation valuation,
                   std::string instanceName)
    : Theory(THEORY_UF, env, out, valuation, instanceName),
      d_thss(nullptr),
      d_lambdaLift(new LambdaLift(env)),
      d_ho(nullptr),
      d_functionsTerms(context()),
      d_symb(env, instanceName),
      d_rewriter(logicInfo().isHigherOrder()),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::uf::" + instanceName, false),
      d_notify(d_im, *this)
{
  d_true = NodeManager::currentNM()->mkConst( true );
  // indicate we are using the default theory state and inference managers
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryUF::~TheoryUF() {
}

TheoryRewriter* TheoryUF::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryUF::getProofChecker() { return &d_checker; }

bool TheoryUF::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = d_instanceName + "theory::uf::ee";
  if (options().quantifiers.finiteModelFind
      && options().uf.ufssMode != options::UfssMode::NONE)
  {
    // need notifications about sorts
    esi.d_notifyNewClass = true;
    esi.d_notifyMerge = true;
    esi.d_notifyDisequal = true;
  }
  return true;
}

void TheoryUF::finishInit() {
  Assert(d_equalityEngine != nullptr);
  // combined cardinality constraints are not evaluated in getModelValue
  d_valuation.setUnevaluatedKind(kind::COMBINED_CARDINALITY_CONSTRAINT);
  // Initialize the cardinality constraints solver if the logic includes UF,
  // finite model finding is enabled, and it is not disabled by
  // the ufssMode option.
  if (options().quantifiers.finiteModelFind
      && options().uf.ufssMode != options::UfssMode::NONE)
  {
    d_thss.reset(new CardinalityExtension(d_env, d_state, d_im, this));
  }
  // The kinds we are treating as function application in congruence
  bool isHo = logicInfo().isHigherOrder();
  d_equalityEngine->addFunctionKind(kind::APPLY_UF, false, isHo);
  if (isHo)
  {
    d_equalityEngine->addFunctionKind(kind::HO_APPLY);
    d_ho.reset(new HoExtension(d_env, d_state, d_im, *d_lambdaLift.get()));
  }
}

static Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */

//--------------------------------- standard check

bool TheoryUF::needsCheckLastEffort()
{
  // last call effort needed if using finite model finding
  return d_thss != nullptr;
}

void TheoryUF::postCheck(Effort level)
{
  if (d_state.isInConflict())
  {
    return;
  }
  // check with the cardinality constraints extension
  if (d_thss != nullptr)
  {
    d_thss->check(level);
  }
  // check with the higher-order extension at full effort
  if (!d_state.isInConflict() && fullEffort(level))
  {
    if (logicInfo().isHigherOrder())
    {
      d_ho->check();
    }
  }
}

void TheoryUF::notifyFact(TNode atom, bool pol, TNode fact, bool isInternal)
{
  if (d_state.isInConflict())
  {
    return;
  }
  if (d_thss != nullptr)
  {
    bool isDecision =
        d_valuation.isSatLiteral(fact) && d_valuation.isDecision(fact);
    d_thss->assertNode(fact, isDecision);
  }
  switch (atom.getKind())
  {
    case kind::EQUAL:
    {
      if (logicInfo().isHigherOrder() && options().uf.ufHoExt)
      {
        if (!pol && !d_state.isInConflict() && atom[0].getType().isFunction())
        {
          // apply extensionality eagerly using the ho extension
          d_ho->applyExtensionality(fact);
        }
      }
    }
    break;
    case kind::CARDINALITY_CONSTRAINT:
    case kind::COMBINED_CARDINALITY_CONSTRAINT:
    {
      if (d_thss == nullptr)
      {
        if (!logicInfo().hasCardinalityConstraints())
        {
          std::stringstream ss;
          ss << "Cardinality constraint " << atom
             << " was asserted, but the logic does not allow it." << std::endl;
          ss << "Try using a logic containing \"UFC\"." << std::endl;
          throw Exception(ss.str());
        }
        else
        {
          // support for cardinality constraints is not enabled, set incomplete
          d_im.setIncomplete(IncompleteId::UF_CARD_DISABLED);
        }
      }
    }
    break;
    default: break;
  }
}
//--------------------------------- end standard check

TrustNode TheoryUF::ppRewrite(TNode node, std::vector<SkolemLemma>& lems)
{
  Trace("uf-exp-def") << "TheoryUF::ppRewrite: expanding definition : " << node
                      << std::endl;
  Kind k = node.getKind();
  bool isHol = logicInfo().isHigherOrder();
  if (k == kind::HO_APPLY || (node.isVar() && node.getType().isFunction()))
  {
    if (!isHol)
    {
      std::stringstream ss;
      ss << "Partial function applications are only supported with "
            "higher-order logic. Try adding the logic prefix HO_.";
      throw LogicException(ss.str());
    }
  }
  else if (k == kind::APPLY_UF)
  {
    if (!isHol && isHigherOrderType(node.getOperator().getType()))
    {
      // check for higher-order
      // logic exception if higher-order is not enabled
      std::stringstream ss;
      ss << "UF received an application whose operator has higher-order type "
         << node
         << ", which is only supported with higher-order logic. Try adding "
            "the logic prefix HO_.";
      throw LogicException(ss.str());
    }
  }
  if (isHol)
  {
    TrustNode ret = d_ho->ppRewrite(node, lems);
    if (!ret.isNull())
    {
      Trace("uf-exp-def") << "TheoryUF::ppRewrite: higher-order: " << node
                          << " to " << ret.getNode() << std::endl;
      return ret;
    }
  }
  return TrustNode::null();
}

void TheoryUF::preRegisterTerm(TNode node)
{
  Debug("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

  if (d_thss != nullptr)
  {
    d_thss->preRegisterTerm(node);
  }

  // we always use APPLY_UF if not higher-order, HO_APPLY if higher-order
  Assert(node.getKind() != kind::HO_APPLY || logicInfo().isHigherOrder());

  Kind k = node.getKind();
  switch (k)
  {
    case kind::EQUAL:
      // Add the trigger for equality
      d_equalityEngine->addTriggerPredicate(node);
      break;
    case kind::APPLY_UF:
    case kind::HO_APPLY:
    {
      // Maybe it's a predicate
      if (node.getType().isBoolean())
      {
        // Get triggered for both equal and dis-equal
        d_equalityEngine->addTriggerPredicate(node);
      }
      else
      {
        // Function applications/predicates
        d_equalityEngine->addTerm(node);
      }
      // Remember the function and predicate terms
      d_functionsTerms.push_back(node);
    }
    break;
  case kind::CARDINALITY_CONSTRAINT:
  case kind::COMBINED_CARDINALITY_CONSTRAINT:
    //do nothing
    break;
  case kind::UNINTERPRETED_CONSTANT:
  {
    // Uninterpreted constants should only appear in models, and should
    // never appear in constraints. They are unallowed to ever appear in
    // constraints since the cardinality of an uninterpreted sort may have
    // an upper bound, e.g. if (forall ((x U) (y U)) (= x y)) holds, then
    // @uc_U_2 is a ill-formed term, as its existence cannot be assumed.
    // The parser prevents the user from ever constructing uninterpreted
    // constants. However, they may be exported via models to API users.
    // It is thus possible that these uninterpreted constants are asserted
    // back in constraints, hence this check is necessary.
    throw LogicException(
        "An uninterpreted constant was preregistered to the UF theory.");
  }
  break;
  default:
    // Variables etc
    d_equalityEngine->addTerm(node);
    break;
  }

  if (logicInfo().isHigherOrder())
  {
    // When using lazy lambda handling, if node is a lambda function, it must
    // be marked as a shared term. This is to ensure we split on the equality
    // of lambda functions with other functions when doing care graph
    // based theory combination.
    if (d_lambdaLift->isLambdaFunction(node))
    {
      addSharedTerm(node);
    }
  }
}

void TheoryUF::explain(TNode literal, Node& exp)
{
  Debug("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL)
  {
    d_equalityEngine->explainEquality(
        atom[0], atom[1], polarity, assumptions, nullptr);
  }
  else
  {
    d_equalityEngine->explainPredicate(atom, polarity, assumptions, nullptr);
  }
  exp = mkAnd(assumptions);
}

TrustNode TheoryUF::explain(TNode literal) { return d_im.explainLit(literal); }

bool TheoryUF::collectModelValues(TheoryModel* m, const std::set<Node>& termSet)
{
  if (logicInfo().isHigherOrder())
  {
    // must add extensionality disequalities for all pairs of (non-disequal)
    // function equivalence classes.
    if (!d_ho->collectModelInfoHo(m, termSet))
    {
      Trace("uf") << "Collect model info fail HO" << std::endl;
      return false;
    }
  }

  Debug("uf") << "UF : finish collectModelInfo " << std::endl;
  return true;
}

void TheoryUF::presolve() {
  // TimerStat::CodeTimer codeTimer(d_presolveTimer);

  Debug("uf") << "uf: begin presolve()" << endl;
  if (options().uf.ufSymmetryBreaker)
  {
    vector<Node> newClauses;
    d_symb.apply(newClauses);
    for(vector<Node>::const_iterator i = newClauses.begin();
        i != newClauses.end();
        ++i) {
      Debug("uf") << "uf: generating a lemma: " << *i << std::endl;
      // no proof generator provided
      d_im.lemma(*i, InferenceId::UF_BREAK_SYMMETRY);
    }
  }
  if( d_thss ){
    d_thss->presolve();
  }
  Debug("uf") << "uf: end presolve()" << endl;
}

void TheoryUF::ppStaticLearn(TNode n, NodeBuilder& learned)
{
  //TimerStat::CodeTimer codeTimer(d_staticLearningTimer);

  vector<TNode> workList;
  workList.push_back(n);
  std::unordered_set<TNode> processed;

  while(!workList.empty()) {
    n = workList.back();

    if (n.isClosure())
    {
      // unsafe to go under quantifiers; we might pull bound vars out of scope!
      processed.insert(n);
      workList.pop_back();
      continue;
    }

    bool unprocessedChildren = false;
    for(TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i) {
      if(processed.find(*i) == processed.end()) {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }

    if(unprocessedChildren) {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if(processed.find(n) != processed.end()) {
      continue;
    }
    processed.insert(n);

    // == DIAMONDS ==

    Debug("diamonds") << "===================== looking at" << endl
                      << n << endl;

    // binary OR of binary ANDs of EQUALities
    if(n.getKind() == kind::OR && n.getNumChildren() == 2 &&
       n[0].getKind() == kind::AND && n[0].getNumChildren() == 2 &&
       n[1].getKind() == kind::AND && n[1].getNumChildren() == 2 &&
       (n[0][0].getKind() == kind::EQUAL) &&
       (n[0][1].getKind() == kind::EQUAL) &&
       (n[1][0].getKind() == kind::EQUAL) &&
       (n[1][1].getKind() == kind::EQUAL)) {
      // now we have (a = b && c = d) || (e = f && g = h)

      Debug("diamonds") << "has form of a diamond!" << endl;

      TNode
        a = n[0][0][0], b = n[0][0][1],
        c = n[0][1][0], d = n[0][1][1],
        e = n[1][0][0], f = n[1][0][1],
        g = n[1][1][0], h = n[1][1][1];

      // test that one of {a, b} = one of {c, d}, and make "b" the
      // shared node (i.e. put in the form (a = b && b = d))
      // note we don't actually care about the shared ones, so the
      // "swaps" below are one-sided, ignoring b and c
      if(a == c) {
        a = b;
      } else if(a == d) {
        a = b;
        d = c;
      } else if(b == c) {
        // nothing to do
      } else if(b == d) {
        d = c;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ A fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ A holds" << endl;

      // same: one of {e, f} = one of {g, h}, and make "f" the
      // shared node (i.e. put in the form (e = f && f = h))
      if(e == g) {
        e = f;
      } else if(e == h) {
        e = f;
        h = g;
      } else if(f == g) {
        // nothing to do
      } else if(f == h) {
        h = g;
      } else {
        // condition not satisfied
        Debug("diamonds") << "+ B fails" << endl;
        continue;
      }

      Debug("diamonds") << "+ B holds" << endl;

      // now we have (a = b && b = d) || (e = f && f = h)
      // test that {a, d} == {e, h}
      if( (a == e && d == h) ||
          (a == h && d == e) ) {
        // learn: n implies a == d
        Debug("diamonds") << "+ C holds" << endl;
        Node newEquality = a.eqNode(d);
        Debug("diamonds") << "  ==> " << newEquality << endl;
        learned << n.impNode(newEquality);
      } else {
        Debug("diamonds") << "+ C fails" << endl;
      }
    }
  }

  if (options().uf.ufSymmetryBreaker)
  {
    d_symb.assertFormula(n);
  }
} /* TheoryUF::ppStaticLearn() */

EqualityStatus TheoryUF::getEqualityStatus(TNode a, TNode b) {

  // Check for equality (simplest)
  if (d_equalityEngine->areEqual(a, b))
  {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }

  // Check for disequality
  if (d_equalityEngine->areDisequal(a, b, false))
  {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }

  // All other terms we interpret as dis-equal in the model
  return EQUALITY_FALSE_IN_MODEL;
}

bool TheoryUF::areCareDisequal(TNode x, TNode y)
{
  if (d_equalityEngine->isTriggerTerm(x, THEORY_UF)
      && d_equalityEngine->isTriggerTerm(y, THEORY_UF))
  {
    TNode x_shared =
        d_equalityEngine->getTriggerTermRepresentative(x, THEORY_UF);
    TNode y_shared =
        d_equalityEngine->getTriggerTermRepresentative(y, THEORY_UF);
    EqualityStatus eqStatus = d_valuation.getEqualityStatus(x_shared, y_shared);
    if (eqStatus == EQUALITY_FALSE || eqStatus == EQUALITY_FALSE_AND_PROPAGATED)
    {
      return true;
    }
    else if (eqStatus == EQUALITY_FALSE_IN_MODEL)
    {
      // if x or y is a lambda function, and they are neither entailed to
      // be equal or disequal, then we return false. This ensures the pair
      // (x,y) may be considered for the care graph.
      if (d_lambdaLift->isLambdaFunction(x)
          || d_lambdaLift->isLambdaFunction(y))
      {
        return false;
      }
      return true;
    }
  }
  return false;
}

void TheoryUF::addCarePairs(const TNodeTrie* t1,
                            const TNodeTrie* t2,
                            unsigned arity,
                            unsigned depth)
{
  // Note we use d_state instead of d_equalityEngine in this method in several
  // places to be robust to cases where the tries have terms that do not
  // exist in the equality engine, which can be the case if higher order.
  if( depth==arity ){
    if( t2!=NULL ){
      Node f1 = t1->getData();
      Node f2 = t2->getData();
      if (!d_state.areEqual(f1, f2))
      {
        Debug("uf::sharing") << "TheoryUf::computeCareGraph(): checking function " << f1 << " and " << f2 << std::endl;
        vector< pair<TNode, TNode> > currentPairs;
        for (size_t k = 0, nchildren = f1.getNumChildren(); k < nchildren; ++k)
        {
          TNode x = f1[k];
          TNode y = f2[k];
          Assert(!d_state.areDisequal(x, y));
          Assert(!areCareDisequal(x, y));
          if (!d_state.areEqual(x, y))
          {
            if (d_equalityEngine->isTriggerTerm(x, THEORY_UF)
                && d_equalityEngine->isTriggerTerm(y, THEORY_UF))
            {
              TNode x_shared =
                  d_equalityEngine->getTriggerTermRepresentative(x, THEORY_UF);
              TNode y_shared =
                  d_equalityEngine->getTriggerTermRepresentative(y, THEORY_UF);
              currentPairs.push_back(make_pair(x_shared, y_shared));
            }
          }
        }
        for (unsigned c = 0; c < currentPairs.size(); ++ c) {
          Debug("uf::sharing") << "TheoryUf::computeCareGraph(): adding to care-graph" << std::endl;
          addCarePair(currentPairs[c].first, currentPairs[c].second);
        }
      }
    }
  }else{
    if( t2==NULL ){
      if( depth<(arity-1) ){
        //add care pairs internal to each child
        for (const std::pair<const TNode, TNodeTrie>& tt : t1->d_data)
        {
          addCarePairs(&tt.second, NULL, arity, depth + 1);
        }
      }
      //add care pairs based on each pair of non-disequal arguments
      for (std::map<TNode, TNodeTrie>::const_iterator it = t1->d_data.begin();
           it != t1->d_data.end();
           ++it)
      {
        std::map<TNode, TNodeTrie>::const_iterator it2 = it;
        ++it2;
        for( ; it2 != t1->d_data.end(); ++it2 ){
          if (!d_state.areDisequal(it->first, it2->first))
          {
            if( !areCareDisequal(it->first, it2->first) ){
              addCarePairs( &it->second, &it2->second, arity, depth+1 );
            }
          }
        }
      }
    }else{
      //add care pairs based on product of indices, non-disequal arguments
      for (const std::pair<const TNode, TNodeTrie>& tt1 : t1->d_data)
      {
        for (const std::pair<const TNode, TNodeTrie>& tt2 : t2->d_data)
        {
          if (!d_state.areDisequal(tt1.first, tt2.first))
          {
            if (!areCareDisequal(tt1.first, tt2.first))
            {
              addCarePairs(&tt1.second, &tt2.second, arity, depth + 1);
            }
          }
        }
      }
    }
  }
}

void TheoryUF::computeCareGraph() {
  if (d_sharedTerms.empty())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  // Use term indexing. We build separate indices for APPLY_UF and HO_APPLY.
  // We maintain indices per operator for the former, and indices per
  // function type for the latter.
  Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Build term indices..."
                       << std::endl;
  // temporary keep set for higher-order indexing below
  std::vector<Node> keep;
  std::map<Node, TNodeTrie> index;
  std::map<TypeNode, TNodeTrie> hoIndex;
  std::map<Node, size_t> arity;
  for (TNode app : d_functionsTerms)
  {
    std::vector<TNode> reps;
    bool has_trigger_arg = false;
    for (const Node& j : app)
    {
      reps.push_back(d_equalityEngine->getRepresentative(j));
      if (d_equalityEngine->isTriggerTerm(j, THEORY_UF))
      {
        has_trigger_arg = true;
      }
    }
    if (has_trigger_arg)
    {
      if (app.getKind() == kind::APPLY_UF)
      {
        Node op = app.getOperator();
        index[op].addTerm(app, reps);
        arity[op] = reps.size();
        if (logicInfo().isHigherOrder() && d_equalityEngine->hasTerm(op))
        {
          // Since we use a lazy app-completion scheme for equating fully
          // and partially applied versions of terms, we must add all
          // sub-chains to the HO index if the operator of this term occurs
          // in a higher-order context in the equality engine.  In other words,
          // for (f a b c), this will add the terms:
          // (HO_APPLY f a), (HO_APPLY (HO_APPLY f a) b),
          // (HO_APPLY (HO_APPLY (HO_APPLY f a) b) c) to the higher-order
          // term index for consideration when computing care pairs.
          Node curr = op;
          for (const Node& c : app)
          {
            Node happ = nm->mkNode(kind::HO_APPLY, curr, c);
            hoIndex[curr.getType()].addTerm(happ, {curr, c});
            curr = happ;
            keep.push_back(happ);
          }
        }
      }
      else
      {
        Assert(app.getKind() == kind::HO_APPLY);
        // add it to the hoIndex for the function type
        hoIndex[app[0].getType()].addTerm(app, reps);
      }
    }
  }
  // for each index
  for (std::pair<const Node, TNodeTrie>& tt : index)
  {
    Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Process index "
                         << tt.first << "..." << std::endl;
    Assert(arity.find(tt.first) != arity.end());
    addCarePairs(&tt.second, nullptr, arity[tt.first], 0);
  }
  for (std::pair<const TypeNode, TNodeTrie>& tt : hoIndex)
  {
    Debug("uf::sharing") << "TheoryUf::computeCareGraph(): Process ho index "
                         << tt.first << "..." << std::endl;
    // the arity of HO_APPLY is always two
    addCarePairs(&tt.second, nullptr, 2, 0);
  }
  Debug("uf::sharing") << "TheoryUf::computeCareGraph(): finished."
                       << std::endl;
}/* TheoryUF::computeCareGraph() */

void TheoryUF::eqNotifyNewClass(TNode t) {
  if (d_thss != NULL) {
    d_thss->newEqClass(t);
  }
}

void TheoryUF::eqNotifyMerge(TNode t1, TNode t2)
{
  if (d_thss != NULL) {
    d_thss->merge(t1, t2);
  }
}

void TheoryUF::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
  if (d_thss != NULL) {
    d_thss->assertDisequal(t1, t2, reason);
  }
}

bool TheoryUF::isHigherOrderType(TypeNode tn)
{
  Assert(tn.isFunction());
  std::map<TypeNode, bool>::iterator it = d_isHoType.find(tn);
  if (it != d_isHoType.end())
  {
    return it->second;
  }
  bool ret = false;
  const std::vector<TypeNode>& argTypes = tn.getArgTypes();
  for (const TypeNode& tnc : argTypes)
  {
    if (tnc.isFunction())
    {
      ret = true;
      break;
    }
  }
  d_isHoType[tn] = ret;
  return ret;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5
