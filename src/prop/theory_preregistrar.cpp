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

class TheoryPreregistrarNotify : public context::ContextNotifyObj
{
 public:
  TheoryPreregistrarNotify(Env& env, TheoryPreregistrar& prr)
      : context::ContextNotifyObj(env.getContext(), false),
        d_env(env),
        d_prr(prr),
        d_sat_literals(env.getUserContext())
  {
  }

  void registerSatLiteral(const Node& literal)
  {
    d_sat_literals.insert(literal, d_env.getContext()->getLevel());
  }

 protected:
  void contextNotifyPop() override
  {
    uint32_t level = d_env.getContext()->getLevel();
    for (auto& p : d_sat_literals)
    {
      if (p.second > level)
      {
        d_prr.notifySatLiteral(p.first);
      }
    }
    if (level == 0)
    {
      d_sat_literals.clear();
    }
  }

 private:
  /** The associated environment. */
  Env& d_env;
  /** The associated theory preregistrar. */
  TheoryPreregistrar& d_prr;
  /**
   * Keep track of sat literals that were registered at a SAT context level > 0
   * and need reregistration when we backtrack to a lower level than the level
   * they were registered at. SAT variables stay in the SAT solver (until they
   * are popped via a user-context-level pop), and we have to ensure that they
   * are registered at all times on the theory level.
   *
   * This is dependent on the user context.
   */
  context::CDHashMap<Node, uint32_t> d_sat_literals;
};

TheoryPreregistrar::TheoryPreregistrar(Env& env,
                                       TheoryEngine* te,
                                       CDCLTSatSolverInterface* ss,
                                       CnfStream* cs)
    : EnvObj(env),
      d_theoryEngine(te),
      d_notify(new TheoryPreregistrarNotify(env, *this))
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
    d_notify->registerSatLiteral(n);
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
