/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory.
 */

#include "theory/sets/theory_sets.h"

#include "options/sets_options.h"
#include "theory/sets/theory_sets_private.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace sets {

TheorySets::TheorySets(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       ProofNodeManager* pnm)
    : Theory(THEORY_SETS, c, u, out, valuation, logicInfo, pnm),
      d_skCache(),
      d_state(c, u, valuation, d_skCache),
      d_im(*this, d_state, nullptr),
      d_internal(new TheorySetsPrivate(*this, d_state, d_im, d_skCache, pnm)),
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
  return true;
}

void TheorySets::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_valuation.setUnevaluatedKind(COMPREHENSION);
  // choice is used to eliminate witness
  d_valuation.setUnevaluatedKind(WITNESS);
  // Universe set is not evaluated. This is moreover important for ensuring that
  // we do not eliminate terms whose value involves the universe set.
  d_valuation.setUnevaluatedKind(UNIVERSE_SET);

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(SINGLETON);
  d_equalityEngine->addFunctionKind(UNION);
  d_equalityEngine->addFunctionKind(INTERSECTION);
  d_equalityEngine->addFunctionKind(SETMINUS);
  d_equalityEngine->addFunctionKind(MEMBER);
  d_equalityEngine->addFunctionKind(SUBSET);
  // relation operators
  d_equalityEngine->addFunctionKind(PRODUCT);
  d_equalityEngine->addFunctionKind(JOIN);
  d_equalityEngine->addFunctionKind(TRANSPOSE);
  d_equalityEngine->addFunctionKind(TCLOSURE);
  d_equalityEngine->addFunctionKind(JOIN_IMAGE);
  d_equalityEngine->addFunctionKind(IDEN);
  d_equalityEngine->addFunctionKind(APPLY_CONSTRUCTOR);
  // we do congruence over cardinality
  d_equalityEngine->addFunctionKind(CARD);

  // finish initialization internally
  d_internal->finishInit();
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

Node TheorySets::getModelValue(TNode node) {
  return Node::null();
}

void TheorySets::preRegisterTerm(TNode node)
{
  d_internal->preRegisterTerm(node);
}

TrustNode TheorySets::ppRewrite(TNode n, std::vector<SkolemLemma>& lems)
{
  Kind nk = n.getKind();
  if (nk == UNIVERSE_SET || nk == COMPLEMENT || nk == JOIN_IMAGE
      || nk == COMPREHENSION)
  {
    if (!options::setsExt())
    {
      std::stringstream ss;
      ss << "Extended set operators are not supported in default mode, try "
            "--sets-ext.";
      throw LogicException(ss.str());
    }
  }
  if (nk == COMPREHENSION)
  {
    // set comprehension is an implicit quantifier, require it in the logic
    if (!getLogicInfo().isQuantified())
    {
      std::stringstream ss;
      ss << "Set comprehensions require quantifiers in the background logic.";
      throw LogicException(ss.str());
    }
  }
  return d_internal->ppRewrite(n, lems);
}

Theory::PPAssertStatus TheorySets::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  Debug("sets-proc") << "ppAssert : " << in << std::endl;
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
      if (!in[0].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitutionSolved(in[0], in[1], tin);
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[1].isVar() && isLegalElimination(in[1], in[0]))
    {
      if (!in[0].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitutionSolved(in[1], in[0], tin);
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[0].isConst() && in[1].isConst())
    {
      if (in[0] != in[1])
      {
        status = Theory::PP_ASSERT_STATUS_CONFLICT;
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

/**************************** eq::NotifyClass *****************************/

void TheorySets::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyNewClass:"
                   << " t = " << t << std::endl;
  d_theory.eqNotifyNewClass(t);
}

void TheorySets::NotifyClass::eqNotifyMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyMerge(t1, t2);
}

void TheorySets::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyDisequal:"
                   << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason
                   << std::endl;
  d_theory.eqNotifyDisequal(t1, t2, reason);
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5
