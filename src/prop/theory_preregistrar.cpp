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
}

TheoryPreregistrar::~TheoryPreregistrar() {}

bool TheoryPreregistrar::needsActiveSkolemDefs() const { return false; }

void TheoryPreregistrar::check() {}

void TheoryPreregistrar::addAssertion(TNode n, TNode skolem, bool isLemma) {}

void TheoryPreregistrar::notifyActiveSkolemDefs(std::vector<TNode>& defs) {}

void TheoryPreregistrar::notifySatLiteral(TNode n)
{
  // if eager policy, send immediately
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    Trace("prereg") << "preregister (eager): " << n << std::endl;
    d_theoryEngine->preRegister(n);
  }
}

bool TheoryPreregistrar::notifyAsserted(TNode n)
{
  // if eager, we've already preregistered it
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    return true;
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
