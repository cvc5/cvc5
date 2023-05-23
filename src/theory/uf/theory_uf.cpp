/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory of uninterpreted functions (UF)
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
#include "theory/arith/arith_utilities.h"
#include "theory/theory_model.h"
#include "theory/type_enumerator.h"
#include "theory/uf/cardinality_extension.h"
#include "theory/uf/conversions_solver.h"
#include "theory/uf/ho_extension.h"
#include "theory/uf/lambda_lift.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace std;

namespace cvc5::internal {
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
      d_rewriter(),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::uf::" + instanceName, false),
      d_notify(d_im, *this),
      d_cpacb(*this)
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
  // conversion kinds
  d_equalityEngine->addFunctionKind(kind::INT_TO_BITVECTOR, true);
  d_equalityEngine->addFunctionKind(kind::BITVECTOR_TO_NAT, true);
}

//--------------------------------- standard check

bool TheoryUF::needsCheckLastEffort()
{
  // last call effort needed if using finite model finding or
  // arithmetic/bit-vector conversions
  return d_thss != nullptr || d_csolver != nullptr;
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
  if (!d_state.isInConflict())
  {
    // check with conversions solver at last call effort
    if (d_csolver != nullptr && level == Effort::EFFORT_LAST_CALL)
    {
      d_csolver->check();
    }
    // check with the higher-order extension at full effort
    if (fullEffort(level) && logicInfo().isHigherOrder())
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
          d_im.setModelUnsound(IncompleteId::UF_CARD_DISABLED);
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
  if (k == kind::HO_APPLY || node.getType().isFunction())
  {
    if (!isHol)
    {
      std::stringstream ss;
      if (k == kind::HO_APPLY)
      {
        ss << "Partial function applications";
      }
      else
      {
        ss << "Function terms";
      }
      ss << " are only supported with "
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
  else if ((k == kind::BITVECTOR_TO_NAT || k == kind::INT_TO_BITVECTOR)
           && options().uf.eagerArithBvConv)
  {
    // eliminate if option specifies to eliminate eagerly
    Node ret = k == kind::BITVECTOR_TO_NAT ? arith::eliminateBv2Nat(node)
                                           : arith::eliminateInt2Bv(node);
    return TrustNode::mkTrustRewrite(node, ret);
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
  Trace("uf") << "TheoryUF::preRegisterTerm(" << node << ")" << std::endl;

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
      d_state.addEqualityEngineTriggerPredicate(node);
      break;
    case kind::APPLY_UF:
    case kind::HO_APPLY:
    {
      // Maybe it's a predicate
      if (node.getType().isBoolean())
      {
        d_state.addEqualityEngineTriggerPredicate(node);
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
    case kind::INT_TO_BITVECTOR:
    case kind::BITVECTOR_TO_NAT:
    {
      Assert(!options().uf.eagerArithBvConv);
      d_equalityEngine->addTerm(node);
      d_functionsTerms.push_back(node);
      // initialize the conversions solver if not already done so
      if (d_csolver == nullptr)
      {
        d_csolver.reset(new ConversionsSolver(d_env, d_state, d_im));
      }
      // call preregister
      d_csolver->preRegisterTerm(node);
    }
    break;
    case kind::CARDINALITY_CONSTRAINT:
    case kind::COMBINED_CARDINALITY_CONSTRAINT:
      // do nothing
      break;
    case kind::UNINTERPRETED_SORT_VALUE:
    {
      // Uninterpreted sort values should only appear in models, and should
      // never appear in constraints. They are unallowed to ever appear in
      // constraints since the cardinality of an uninterpreted sort may have an
      // upper bound, e.g. if (forall ((x U) (y U)) (= x y)) holds, then @uc_U_2
      // is a ill-formed term, as its existence cannot be assumed.  The parser
      // prevents the user from ever constructing uninterpreted sort values.
      // However, they may be exported via models to API users. It is thus
      // possible that these uninterpreted sort values are asserted back in
      // constraints, hence this check is necessary.
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
  Trace("uf") << "TheoryUF::explain(" << literal << ")" << std::endl;
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
  exp = NodeManager::currentNM()->mkAnd(assumptions);
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

  Trace("uf") << "UF : finish collectModelInfo " << std::endl;
  return true;
}

void TheoryUF::presolve() {
  // TimerStat::CodeTimer codeTimer(d_presolveTimer);

  Trace("uf") << "uf: begin presolve()" << endl;
  if (options().uf.ufSymmetryBreaker)
  {
    vector<Node> newClauses;
    d_symb.apply(newClauses);
    for(vector<Node>::const_iterator i = newClauses.begin();
        i != newClauses.end();
        ++i) {
      Trace("uf") << "uf: generating a lemma: " << *i << std::endl;
      // no proof generator provided
      d_im.lemma(*i, InferenceId::UF_BREAK_SYMMETRY);
    }
  }
  if( d_thss ){
    d_thss->presolve();
  }
  Trace("uf") << "uf: end presolve()" << endl;
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

    Trace("diamonds") << "===================== looking at" << endl
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

      Trace("diamonds") << "has form of a diamond!" << endl;

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
        Trace("diamonds") << "+ A fails" << endl;
        continue;
      }

      Trace("diamonds") << "+ A holds" << endl;

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
        Trace("diamonds") << "+ B fails" << endl;
        continue;
      }

      Trace("diamonds") << "+ B holds" << endl;

      // now we have (a = b && b = d) || (e = f && f = h)
      // test that {a, d} == {e, h}
      if( (a == e && d == h) ||
          (a == h && d == e) ) {
        // learn: n implies a == d
        Trace("diamonds") << "+ C holds" << endl;
        Node newEquality = a.eqNode(d);
        Trace("diamonds") << "  ==> " << newEquality << endl;
        learned << n.impNode(newEquality);
      } else {
        Trace("diamonds") << "+ C fails" << endl;
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

void TheoryUF::processCarePairArgs(TNode a, TNode b)
{
  // if a and b are already equal, we ignore this pair
  if (d_state.areEqual(a, b))
  {
    return;
  }
  // otherwise, we add pairs for each of their arguments
  addCarePairArgs(a, b);
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
  Trace("uf::sharing") << "TheoryUf::computeCareGraph(): Build term indices..."
                       << std::endl;
  // temporary keep set for higher-order indexing below
  std::vector<Node> keep;
  std::map<Node, TNodeTrie> index;
  std::map<TypeNode, TNodeTrie> typeIndex;
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
      Trace("uf::sharing-terms")
          << "...add: " << app << " / " << reps << std::endl;
      Kind k = app.getKind();
      if (k == kind::APPLY_UF)
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
            Assert(curr.getType().isFunction());
            typeIndex[curr.getType()].addTerm(happ, {curr, c});
            curr = happ;
            keep.push_back(happ);
          }
        }
      }
      else if (k == kind::HO_APPLY || k == kind::BITVECTOR_TO_NAT)
      {
        // add it to the typeIndex for the function type if HO_APPLY, or the
        // bitvector type if bv2nat. The latter ensures that we compute
        // care pairs based on bv2nat only for bitvectors of the same width.
        typeIndex[app[0].getType()].addTerm(app, reps);
      }
      else
      {
        // case for other operators, e.g. int2bv
        Node op = app.getOperator();
        index[op].addTerm(app, reps);
        arity[op] = reps.size();
      }
    }
  }
  // for each index
  for (std::pair<const Node, TNodeTrie>& tt : index)
  {
    Trace("uf::sharing") << "TheoryUf::computeCareGraph(): Process index "
                         << tt.first << "..." << std::endl;
    Assert(arity.find(tt.first) != arity.end());
    nodeTriePathPairProcess(&tt.second, arity[tt.first], d_cpacb);
  }
  for (std::pair<const TypeNode, TNodeTrie>& tt : typeIndex)
  {
    // functions for HO_APPLY which has arity 2, bitvectors for bv2nat which
    // has arity one
    size_t a = tt.first.isFunction() ? 2 : 1;
    Trace("uf::sharing") << "TheoryUf::computeCareGraph(): Process ho index "
                         << tt.first << "..." << std::endl;
    // the arity of HO_APPLY is always two
    nodeTriePathPairProcess(&tt.second, a, d_cpacb);
  }
  Trace("uf::sharing") << "TheoryUf::computeCareGraph(): finished."
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
}  // namespace cvc5::internal
