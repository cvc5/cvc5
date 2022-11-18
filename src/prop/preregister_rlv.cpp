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
 * Preregister relevant formulas
 */

#include "prop/preregister_rlv.h"

#include "options/prop_options.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace prop {

PreregisterRlv::PreregisterRlv(Env& env, TheoryEngine* te)
    : EnvObj(env), d_theoryEngine(te)
{
}

PreregisterRlv::~PreregisterRlv() {}

bool PreregisterRlv::needsActiveSkolemDefs() const
{
  return options().prop.preRegisterMode == options::PreRegisterMode::RELEVANT;
}

void PreregisterRlv::notifyAssertion(TNode n, TNode skolem, bool isLemma)
{
  if (options().prop.preRegisterMode != options::PreRegisterMode::RELEVANT)
  {
    return;
  }
  // TODO
}

void PreregisterRlv::notifyActiveSkolemDefs(std::vector<TNode>& defs)
{
  if (options().prop.preRegisterMode != options::PreRegisterMode::RELEVANT)
  {
    return;
  }
  // TODO
}

void PreregisterRlv::notifyPreRegister(TNode n)
{
  // if eager policy, send immediately
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    d_theoryEngine->preRegister(n);
  }
}

void PreregisterRlv::notifyAsserted(TNode n)
{
  // if eager, we've already preregistered it
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    return;
  }
  // otherwise, we always ensure it is preregistered now
  Node natom = n.getKind() == kind::NOT ? n[0] : n;
  d_theoryEngine->preRegister(natom);
}

void PreregisterRlv::preRegisterToTheory(const std::vector<Node>& toPreregister)
{
  for (const Node& n : toPreregister)
  {
    Trace("ajr-temp") << "preregister: " << n << std::endl;
    d_theoryEngine->preRegister(n);
  }
}

}  // namespace prop
}  // namespace cvc5::internal
