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

TheoryPreregistrar::TheoryPreregistrar(Env& env, TheoryEngine* te,
                 CDCLTSatSolverInterface* ss,
                 CnfStream* cs)
    : EnvObj(env), d_theoryEngine(te)
{
  if (options().prop.preRegisterMode == options::PreRegisterMode::RELEVANT)
  {
    d_propFinder.reset(new decision::PropFinder(d_env, ss, cs));
  }
}

TheoryPreregistrar::~TheoryPreregistrar() {}

bool TheoryPreregistrar::needsActiveSkolemDefs() const
{
  return options().prop.preRegisterMode == options::PreRegisterMode::RELEVANT;
}

void TheoryPreregistrar::addAssertion(TNode n, TNode skolem, bool isLemma)
{
  if (d_propFinder != nullptr)
  {
    std::vector<TNode> toPreregister;
    d_propFinder->addAssertion(n, skolem, isLemma, toPreregister);
    preRegisterToTheory(toPreregister);
  }
}

void TheoryPreregistrar::notifyActiveSkolemDefs(std::vector<TNode>& defs)
{
  if (d_propFinder != nullptr)
  {
    std::vector<TNode> toPreregister;
    d_propFinder->notifyActiveSkolemDefs(defs, toPreregister);
    preRegisterToTheory(toPreregister);
  }
}

void TheoryPreregistrar::notifyPreRegister(TNode n)
{
  // if eager policy, send immediately
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    d_theoryEngine->preRegister(n);
  }
}

void TheoryPreregistrar::notifyAsserted(TNode n)
{
  // if eager, we've already preregistered it
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    return;
  }
  // if we are using the propagation finder, use it
  if (d_propFinder != nullptr)
  {
    std::vector<TNode> toPreregister;
    d_propFinder->notifyAsserted(n, toPreregister);
    preRegisterToTheory(toPreregister);
    return;
  }
  // otherwise, we always ensure it is preregistered now, which does nothing
  // if it is already preregistered
  Node natom = n.getKind() == kind::NOT ? n[0] : n;
  d_theoryEngine->preRegister(natom);
}

void TheoryPreregistrar::preRegisterToTheory(
    const std::vector<TNode>& toPreregister)
{
  for (TNode n : toPreregister)
  {
    d_theoryEngine->preRegister(n);
  }
}

}  // namespace prop
}  // namespace cvc5::internal
