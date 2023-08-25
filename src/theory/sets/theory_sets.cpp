/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory.
 */

#include "theory/sets/theory_sets.h"

#include "options/sets_options.h"
#include "theory/sets/set_reduction.h"
#include "theory/sets/theory_sets_private.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace sets {

TheorySets::TheorySets(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_SETS, env, out, valuation),
      d_skCache(env.getRewriter()),
      d_state(env, valuation, d_skCache),
      d_im(env, *this, d_state),
      d_cpacb(*this),
      d_internal(
          new TheorySetsPrivate(env, *this, d_state, d_im, d_skCache, d_cpacb)),
      d_notify(*d_internal.get(), d_im)
{
  // use the official theory state and inference manager objects
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheorySets::~TheorySets()
{
}

TheoryRewriter* TheorySets::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

ProofRuleChecker* TheorySets::getProofChecker() { return nullptr; }

bool TheorySets::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::sets::ee";
  esi.d_notifyNewClass = true;
  esi.d_notifyMerge = true;
  esi.d_notifyDisequal = true;
  return true;
}

void TheorySets::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_valuation.setUnevaluatedKind(SET_COMPREHENSION);
  // choice is used to eliminate witness
  d_valuation.setUnevaluatedKind(WITNESS);
  // Universe set is not evaluated. This is moreover important for ensuring that
  // we do not eliminate terms whose value involves the universe set.
  d_valuation.setUnevaluatedKind(SET_UNIVERSE);

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(SET_SINGLETON);
  d_equalityEngine->addFunctionKind(SET_UNION);
  d_equalityEngine->addFunctionKind(SET_INTER);
  d_equalityEngine->addFunctionKind(SET_MINUS);
  d_equalityEngine->addFunctionKind(SET_MEMBER);
  d_equalityEngine->addFunctionKind(SET_SUBSET);
  // relation operators
  d_equalityEngine->addFunctionKind(RELATION_PRODUCT);
  d_equalityEngine->addFunctionKind(RELATION_JOIN);
  d_equalityEngine->addFunctionKind(RELATION_TRANSPOSE);
  d_equalityEngine->addFunctionKind(RELATION_TCLOSURE);
  d_equalityEngine->addFunctionKind(RELATION_JOIN_IMAGE);
  d_equalityEngine->addFunctionKind(RELATION_IDEN);
  d_equalityEngine->addFunctionKind(APPLY_CONSTRUCTOR);
  // we do congruence over cardinality
  d_equalityEngine->addFunctionKind(SET_CARD);

  // finish initialization internally
  d_internal->finishInit();

  // memberships are not relevant for model building
  d_valuation.setIrrelevantKind(SET_MEMBER);
}

void TheorySets::postCheck(Effort level) { d_internal->postCheck(level); }

void TheorySets::notifyFact(TNode atom,
                            bool polarity,
                            TNode fact,
                            bool isInternal)
{
  d_internal->notifyFact(atom, polarity, fact);
}

bool TheorySets::collectModelValues(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  return d_internal->collectModelValues(m, termSet);
}

void TheorySets::computeCareGraph() {
  d_internal->computeCareGraph();
}

TrustNode TheorySets::explain(TNode node)
{
  Node exp = d_internal->explain(node);
  return TrustNode::mkTrustPropExp(node, exp, nullptr);
}

Node TheorySets::getCandidateModelValue(TNode node) { return Node::null(); }

void TheorySets::preRegisterTerm(TNode node)
{
  d_internal->preRegisterTerm(node);
}

TrustNode TheorySets::ppRewrite(TNode n, std::vector<SkolemLemma>& lems)
{
  Kind nk = n.getKind();
  if (nk == SET_UNIVERSE || nk == SET_COMPLEMENT || nk == RELATION_JOIN_IMAGE
      || nk == SET_COMPREHENSION)
  {
    if (!options().sets.setsExt)
    {
      std::stringstream ss;
      ss << "Extended set operators are not supported in default mode, try "
            "--sets-ext.";
      throw LogicException(ss.str());
    }
  }
  if (nk == SET_COMPREHENSION)
  {
    // set comprehension is an implicit quantifier, require it in the logic
    if (!logicInfo().isQuantified())
    {
      std::stringstream ss;
      ss << "Set comprehensions require quantifiers in the background logic.";
      throw LogicException(ss.str());
    }
  }
  if (nk == RELATION_AGGREGATE || nk == RELATION_PROJECT || nk == SET_MAP
      || nk == SET_FOLD)
  {
    // requires higher order
    if (!logicInfo().isHigherOrder())
    {
      std::stringstream ss;
      ss << "Term of kind " << nk
         << " are only supported with "
            "higher-order logic. Try adding the logic prefix HO_.";
      throw LogicException(ss.str());
    }
  }
  if (nk == SET_FOLD)
  {
    std::vector<Node> asserts;
    Node ret = SetReduction::reduceFoldOperator(n, asserts);
    NodeManager* nm = NodeManager::currentNM();
    Node andNode = nm->mkNode(AND, asserts);
    d_im.lemma(andNode, InferenceId::SETS_FOLD);
    return TrustNode::mkTrustRewrite(n, ret, nullptr);
  }
  if (nk == RELATION_AGGREGATE)
  {
    Node ret = SetReduction::reduceAggregateOperator(n);
    return TrustNode::mkTrustRewrite(ret, ret, nullptr);
  }
  if (nk == RELATION_PROJECT)
  {
    Node ret = SetReduction::reduceProjectOperator(n);
    return TrustNode::mkTrustRewrite(ret, ret, nullptr);
  }
  return d_internal->ppRewrite(n, lems);
}

Theory::PPAssertStatus TheorySets::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  Trace("sets-proc") << "ppAssert : " << in << std::endl;
  Theory::PPAssertStatus status = Theory::PP_ASSERT_STATUS_UNSOLVED;

  // this is based off of Theory::ppAssert
  if (in.getKind() == EQUAL)
  {
    if (in[0].isVar() && isLegalElimination(in[0], in[1]))
    {
      // We cannot solve for sets if setsExt is enabled, since universe set
      // may appear when this option is enabled, and solving for such a set
      // impacts the semantics of universe set, see
      // regress0/sets/pre-proc-univ.smt2
      if (!in[0].getType().isSet() || !options().sets.setsExt)
      {
        outSubstitutions.addSubstitutionSolved(in[0], in[1], tin);
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[1].isVar() && isLegalElimination(in[1], in[0]))
    {
      if (!in[0].getType().isSet() || !options().sets.setsExt)
      {
        outSubstitutions.addSubstitutionSolved(in[1], in[0], tin);
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
  }
  return status;
}

void TheorySets::presolve() {
  d_internal->presolve();
}

bool TheorySets::isEntailed( Node n, bool pol ) {
  return d_internal->isEntailed( n, pol );
}

void TheorySets::processCarePairArgs(TNode a, TNode b)
{
  // Usually when (= (f x) (f y)), we don't care whether (= x y) is true or
  // not for the shared variables x, y in the care graph.
  // However, this does not apply to the membership operator since the
  // equality or disequality between members affects the number of elements
  // in a set. Therefore we need to split on (= x y) for kind SET_MEMBER.
  // Example:
  // Suppose (set.member x S) = (set.member y S) = true and there are
  // no other members in S. We would get S = {x} if (= x y) is true.
  // Otherwise we would get S = {x, y}.
  if (a.getKind() != SET_MEMBER && d_state.areEqual(a, b))
  {
    return;
  }
  // otherwise, we add pairs for each of their arguments
  addCarePairArgs(a, b);

  d_internal->processCarePairArgs(a, b);
}

/**************************** eq::NotifyClass *****************************/

void TheorySets::NotifyClass::eqNotifyNewClass(TNode t)
{
  Trace("sets-eq") << "[sets-eq] eqNotifyNewClass:"
                   << " t = " << t << std::endl;
  d_theory.eqNotifyNewClass(t);
}

void TheorySets::NotifyClass::eqNotifyMerge(TNode t1, TNode t2)
{
  Trace("sets-eq") << "[sets-eq] eqNotifyMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyMerge(t1, t2);
}

void TheorySets::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Trace("sets-eq") << "[sets-eq] eqNotifyDisequal:"
                   << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason
                   << std::endl;
  d_theory.eqNotifyDisequal(t1, t2, reason);
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
