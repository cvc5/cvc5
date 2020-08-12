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
      d_internal(new TheorySetsPrivate(*this, c, u)),
      d_notify(*d_internal.get()),
      d_equalityEngine(d_notify, c, "theory::sets::ee", true)
{
  // Do not move me to the header.
  // The constructor + destructor are not in the header as d_internal is a
  // unique_ptr<TheorySetsPrivate> and TheorySetsPrivate is an opaque type in
  // the header (Pimpl). See https://herbsutter.com/gotw/_100/ .
}

TheorySets::~TheorySets()
{
  // Do not move me to the header. See explanation in the constructor.
}

TheoryRewriter* TheorySets::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

void TheorySets::finishInit()
{
  d_valuation.setUnevaluatedKind(COMPREHENSION);
  // choice is used to eliminate witness
  d_valuation.setUnevaluatedKind(WITNESS);

  // functions we are doing congruence over
  d_equalityEngine.addFunctionKind(kind::SINGLETON);
  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);
  d_equalityEngine.addFunctionKind(kind::MEMBER);
  d_equalityEngine.addFunctionKind(kind::SUBSET);
  // relation operators
  d_equalityEngine.addFunctionKind(PRODUCT);
  d_equalityEngine.addFunctionKind(JOIN);
  d_equalityEngine.addFunctionKind(TRANSPOSE);
  d_equalityEngine.addFunctionKind(TCLOSURE);
  d_equalityEngine.addFunctionKind(JOIN_IMAGE);
  d_equalityEngine.addFunctionKind(IDEN);
  d_equalityEngine.addFunctionKind(APPLY_CONSTRUCTOR);
  // we do congruence over cardinality
  d_equalityEngine.addFunctionKind(CARD);

  // finish initialization internally
  d_internal->finishInit();
}

void TheorySets::addSharedTerm(TNode n) {
  d_internal->addSharedTerm(n);
}

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

void TheorySets::propagate(Effort e) {
  d_internal->propagate(e);
}

bool TheorySets::isEntailed( Node n, bool pol ) {
  return d_internal->isEntailed( n, pol );
}

eq::EqualityEngine* TheorySets::getEqualityEngine() 
{
  return &d_equalityEngine;
}

void TheorySets::setMasterEqualityEngine(eq::EqualityEngine* eq)
{
  d_equalityEngine.setMasterEqualityEngine(eq);
}

/**************************** eq::NotifyClass *****************************/

bool TheorySets::NotifyClass::eqNotifyTriggerEquality(TNode equality,
                                                      bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerEquality: equality = "
                   << equality << " value = " << value << std::endl;
  if (value)
  {
    return d_theory.propagate(equality);
  }
  else
  {
    // We use only literal triggers so taking not is safe
    return d_theory.propagate(equality.notNode());
  }
}

bool TheorySets::NotifyClass::eqNotifyTriggerPredicate(TNode predicate,
                                                       bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = "
                   << predicate << " value = " << value << std::endl;
  if (value)
  {
    return d_theory.propagate(predicate);
  }
  else
  {
    return d_theory.propagate(predicate.notNode());
  }
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

void TheorySets::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPreMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyPreMerge(t1, t2);
}

void TheorySets::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyPostMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyPostMerge(t1, t2);
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
