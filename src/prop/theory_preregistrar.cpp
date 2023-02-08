/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preregister policy
 */

#include "prop/theory_preregistrar.h"

#include "options/prop_options.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace prop {

TheoryPreregistrar::TheoryPreregistrar(Env& env,
                                       TheoryEngine* te,
                                       CDCLTSatSolverInterface* ss,
                                       CnfStream* cs)
    : EnvObj(env), d_theoryEngine(te)
{
  if (options().prop.preRegisterMode == options::PreRegisterMode::RELEVANT)
  {
    d_rlvPrereg.reset(new RelevantPreregistrar(d_env, ss, cs));
  }
}

TheoryPreregistrar::~TheoryPreregistrar() {}

bool TheoryPreregistrar::needsActiveSkolemDefs() const
{
  return options().prop.preRegisterMode == options::PreRegisterMode::RELEVANT;
}

void TheoryPreregistrar::check()
{
  if (d_rlvPrereg != nullptr)
  {
    std::vector<TNode> toPreregister;
    d_rlvPrereg->check(toPreregister);
    preRegisterToTheory(toPreregister);
  }
}

void TheoryPreregistrar::addAssertion(TNode n, TNode skolem, bool isLemma)
{
  if (d_rlvPrereg != nullptr)
  {
    // notice this does not trigger preregistration, instead the assertions
    // are buffered
    d_rlvPrereg->addAssertion(n, skolem, isLemma);
  }
}

void TheoryPreregistrar::notifyActiveSkolemDefs(std::vector<TNode>& defs)
{
  if (d_rlvPrereg != nullptr)
  {
    std::vector<TNode> toPreregister;
    d_rlvPrereg->notifyActiveSkolemDefs(defs, toPreregister);
    preRegisterToTheory(toPreregister);
  }
}

void TheoryPreregistrar::notifySatLiteral(TNode n)
{
  // if eager policy, send immediately
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    Trace("prereg") << "preregister (eager): " << n << std::endl;
    d_theoryEngine->preRegister(n);
  }
  else if (d_rlvPrereg != nullptr)
  {
    d_rlvPrereg->notifySatLiteral(n);
  }
}

bool TheoryPreregistrar::notifyAsserted(TNode n)
{
  // if eager, we've already preregistered it
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    return true;
  }
  // if we are using the propagation finder, use it
  if (d_rlvPrereg != nullptr)
  {
    std::vector<TNode> toPreregister;
    bool ret = d_rlvPrereg->notifyAsserted(n, toPreregister);
    preRegisterToTheory(toPreregister);
    return ret;
  }
  // otherwise, we always ensure it is preregistered now, which does nothing
  // if it is already preregistered
  TNode natom = n.getKind() == kind::NOT ? n[0] : n;
  Trace("prereg") << "preregister (lazy): " << natom << std::endl;
  d_theoryEngine->preRegister(natom);
  return true;
}

void TheoryPreregistrar::preRegisterToTheory(
    const std::vector<TNode>& toPreregister)
{
  for (TNode n : toPreregister)
  {
    Trace("prereg") << "preregister: " << n << std::endl;
    d_theoryEngine->preRegister(n);
  }
}

}  // namespace prop
}  // namespace cvc5::internal
