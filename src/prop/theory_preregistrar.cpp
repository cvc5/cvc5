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
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace prop {

TheoryPreregistrar::TheoryPreregistrar(Env& env,
                                       TheoryEngine* te,
                                       CDCLTSatSolver* ss,
                                       CnfStream* cs)
    : EnvObj(env), d_theoryEngine(te)
{
}

TheoryPreregistrar::~TheoryPreregistrar() {}

bool TheoryPreregistrar::needsActiveSkolemDefs() const { return false; }

void TheoryPreregistrar::check()
{
  uint32_t level = d_env.getContext()->getLevel();
  std::vector<TNode> to_erase;
  for (auto& p : d_sat_literals)
  {
    if (!d_theoryEngine->getPropEngine()->getCnfStream()->hasLiteral(p.first))
    {
      to_erase.push_back(p.first);
    }
    else if (p.second > level)
    {
      notifySatLiteral(p.first);
      p.second = level;
    }
  }
  if (level == 0)
  {
    d_sat_literals.clear();
  }
  else
  {
    for (const auto& node : to_erase)
    {
      d_sat_literals.erase(node);
    }
  }
}

void TheoryPreregistrar::addAssertion(TNode n, TNode skolem, bool isLemma) {}

void TheoryPreregistrar::notifyActiveSkolemDefs(std::vector<TNode>& defs) {}

void TheoryPreregistrar::notifySatLiteral(TNode n)
{
  // if eager policy, send immediately
  if (options().prop.preRegisterMode == options::PreRegisterMode::EAGER)
  {
    Trace("prereg") << "preregister (eager): " << n << std::endl;
    d_theoryEngine->preRegister(n);
    d_sat_literals.emplace(n, d_env.getContext()->getLevel());
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
