/*********************                                                        */
/*! \file theory_sets.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory.
 **
 ** Sets theory.
 **/

#include "theory/sets/theory_sets.h"

#include "options/sets_options.h"
#include "theory/sets/theory_sets_private.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

TheorySets::TheorySets(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       ProofNodeManager* pnm)
    : Theory(THEORY_SETS, c, u, out, valuation, logicInfo, pnm),
      d_internal(new TheorySetsPrivate(*this, c, u, valuation)),
      d_notify(*d_internal.get())
{
  // use the state object as the official theory state
  d_theoryState = d_internal->getSolverState();
}

TheorySets::~TheorySets()
{
  // Do not move me to the header. See explanation in the constructor.
}

TheoryRewriter* TheorySets::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

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

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(kind::SINGLETON);
  d_equalityEngine->addFunctionKind(kind::UNION);
  d_equalityEngine->addFunctionKind(kind::INTERSECTION);
  d_equalityEngine->addFunctionKind(kind::SETMINUS);
  d_equalityEngine->addFunctionKind(kind::MEMBER);
  d_equalityEngine->addFunctionKind(kind::SUBSET);
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

void TheorySets::notifySharedTerm(TNode n) { d_internal->addSharedTerm(n); }

void TheorySets::check(Effort e) {
  if (done() && e < Theory::EFFORT_FULL) {
    return;
  }
  TimerStat::CodeTimer checkTimer(d_checkTime);
  d_internal->check(e);
}

bool TheorySets::collectModelInfo(TheoryModel* m)
{
  return d_internal->collectModelInfo(m);
}

void TheorySets::computeCareGraph() {
  d_internal->computeCareGraph();
}

TrustNode TheorySets::explain(TNode node)
{
  Node exp = d_internal->explain(node);
  return TrustNode::mkTrustPropExp(node, exp, nullptr);
}

EqualityStatus TheorySets::getEqualityStatus(TNode a, TNode b) {
  return d_internal->getEqualityStatus(a, b);
}

Node TheorySets::getModelValue(TNode node) {
  return Node::null();
}

void TheorySets::preRegisterTerm(TNode node) {
  d_internal->preRegisterTerm(node);
}

TrustNode TheorySets::expandDefinition(Node n)
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
  return d_internal->expandDefinition(n);
}

Theory::PPAssertStatus TheorySets::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  Debug("sets-proc") << "ppAssert : " << in << std::endl;
  Theory::PPAssertStatus status = Theory::PP_ASSERT_STATUS_UNSOLVED;

  // this is based off of Theory::ppAssert
  if (in.getKind() == kind::EQUAL)
  {
    if (in[0].isVar() && isLegalElimination(in[0], in[1]))
    {
      // We cannot solve for sets if setsExt is enabled, since universe set
      // may appear when this option is enabled, and solving for such a set
      // impacts the semantics of universe set, see
      // regress0/sets/pre-proc-univ.smt2
      if (!in[0].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitution(in[0], in[1]);
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[1].isVar() && isLegalElimination(in[1], in[0]))
    {
      if (!in[0].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitution(in[1], in[0]);
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

bool TheorySets::NotifyClass::eqNotifyTriggerPredicate(TNode predicate,
                                                       bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = "
                   << predicate << " value = " << value << std::endl;
  if (value)
  {
    return d_theory.propagate(predicate);
  }
  return d_theory.propagate(predicate.notNode());
}

bool TheorySets::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag,
                                                          TNode t1,
                                                          TNode t2,
                                                          bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerTermEquality: tag = " << tag
                   << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value
                   << std::endl;
  d_theory.propagate(value ? t1.eqNode(t2) : t1.eqNode(t2).negate());
  return true;
}

void TheorySets::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyConstantTermMerge "
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}

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

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
