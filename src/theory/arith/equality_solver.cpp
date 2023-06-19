/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic equality solver
 */

#include "theory/arith/equality_solver.h"

#include "theory/arith/inference_manager.h"
#include "theory/arith/linear/congruence_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

EqualitySolver::EqualitySolver(Env& env,
                               TheoryState& astate,
                               InferenceManager& aim)
    : EnvObj(env),
      d_astate(astate),
      d_aim(aim),
      d_notify(*this),
      d_ee(nullptr),
      d_propLits(context()),
      d_acm(nullptr)
{
}

bool EqualitySolver::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "arith::ee";
  return true;
}

void EqualitySolver::finishInit()
{
  d_ee = d_astate.getEqualityEngine();
  // add the function kinds
  d_ee->addFunctionKind(kind::NONLINEAR_MULT);
  d_ee->addFunctionKind(kind::EXPONENTIAL);
  d_ee->addFunctionKind(kind::SINE);
  d_ee->addFunctionKind(kind::IAND);
  d_ee->addFunctionKind(kind::POW2);
}

bool EqualitySolver::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  if (atom.getKind() != EQUAL)
  {
    // finished processing, since not beneficial to add non-equality facts
    return true;
  }
  Trace("arith-eq-solver") << "EqualitySolver::preNotifyFact: " << fact
                           << std::endl;
  // we will process
  return false;
}

TrustNode EqualitySolver::explain(TNode lit)
{
  Trace("arith-eq-solver-debug") << "explain " << lit << "?" << std::endl;
  if (d_acm != nullptr)
  {
    // if we are using the congruence manager, consult whether it can explain
    if (d_acm->canExplain(lit))
    {
      return d_acm->explain(lit);
    }
    // otherwise, don't explain
    return TrustNode::null();
  }
  // check if we propagated it?
  if (d_propLits.find(lit) == d_propLits.end())
  {
    Trace("arith-eq-solver-debug") << "...did not propagate" << std::endl;
    return TrustNode::null();
  }
  Trace("arith-eq-solver-debug")
      << "...explain via inference manager" << std::endl;
  // if we did, explain with the arithmetic inference manager
  return d_aim.explainLit(lit);
}

void EqualitySolver::setCongruenceManager(linear::ArithCongruenceManager* acm)
{
  d_acm = acm;
}

bool EqualitySolver::propagateLit(Node lit)
{
  if (d_acm != nullptr)
  {
    // if we are using the congruence manager, notify it
    return d_acm->propagate(lit);
  }
  // if we've already propagated, ignore
  if (d_aim.hasPropagated(lit))
  {
    return true;
  }
  // notice this is only used when ee-mode=distributed
  // remember that this was a literal we propagated
  Trace("arith-eq-solver-debug") << "propagate lit " << lit << std::endl;
  d_propLits.insert(lit);
  return d_aim.propagateLit(lit);
}
void EqualitySolver::conflictEqConstantMerge(TNode a, TNode b)
{
  if (d_acm != nullptr)
  {
    // if we are using the congruence manager, notify it
    Node eq = a.eqNode(b);
    d_acm->propagate(eq);
    return;
  }
  d_aim.conflictEqConstantMerge(a, b);
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerPredicate(
    TNode predicate, bool value)
{
  Trace("arith-eq-solver") << "...propagate (predicate) " << predicate << " -> "
                           << value << std::endl;
  if (value)
  {
    return d_es.propagateLit(predicate);
  }
  return d_es.propagateLit(predicate.notNode());
}

bool EqualitySolver::EqualitySolverNotify::eqNotifyTriggerTermEquality(
    TheoryId tag, TNode t1, TNode t2, bool value)
{
  Trace("arith-eq-solver") << "...propagate (term eq) " << t1.eqNode(t2)
                           << " -> " << value << std::endl;
  if (value)
  {
    return d_es.propagateLit(t1.eqNode(t2));
  }
  return d_es.propagateLit(t1.eqNode(t2).notNode());
}

void EqualitySolver::EqualitySolverNotify::eqNotifyConstantTermMerge(TNode t1,
                                                                     TNode t2)
{
  Trace("arith-eq-solver") << "...conflict merge " << t1 << " " << t2
                           << std::endl;
  d_es.conflictEqConstantMerge(t1, t2);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
