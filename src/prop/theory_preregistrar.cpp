/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "prop/sat_solver.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace prop {

/* -------------------------------------------------------------------------- */

/**
 * The context notify object for the theory preregistrar. Clears the
 * reregistration cache on user context pop.
 */
class TheoryPreregistrarNotify : public context::ContextNotifyObj
{
 public:
  TheoryPreregistrarNotify(Env& env, TheoryPreregistrar& prr)
      : context::ContextNotifyObj(env.getUserContext(), false), d_prr(prr)
  {
  }

 protected:
  void contextNotifyPop() override { d_prr.d_sat_literals.clear(); }

 private:
  /** The associated theory preregistrar. */
  TheoryPreregistrar& d_prr;
};

/* -------------------------------------------------------------------------- */

TheoryPreregistrar::TheoryPreregistrar(Env& env,
                                       TheoryEngine* te,
                                       CDCLTSatSolver* ss,
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
    // cache for registration
    d_sat_literals.emplace_back(n, d_env.getContext()->getLevel());
  }
}

void TheoryPreregistrar::notifyBacktrack(uint32_t nlevels)
{
  (void)nlevels;

  uint32_t level = d_env.getContext()->getLevel();
  for (size_t i = 0, n = d_sat_literals.size(); i < n; ++i)
  {
    // We reregister SAT literals from newest to oldest. Changing this order
    // potentially has an impact on performance (quantified instances).
    auto& [node, node_level] = d_sat_literals[n - i - 1];

    if (node_level <= level)
    {
      break;
    }

    // Update SAT context level the reregistered SAT literal has been
    // registered at. This is necessary to not reregister literals that
    // are already registered.
    node_level = level;
    // Reregister all sat literals that have originally been preregistered
    // at a higher level than the current SAT context level. These literals
    // are popped from the SAT context on backtrack but remain in the SAT
    // solver, and thus must be reregistered.
    Trace("prereg") << "reregister: " << n << std::endl;
    // Note: This call potentially adds to d_sat_literals, which we are
    //       currently iterating over. This is not an issue, though, since
    //       a) we access it by index and b) any literals added through this
    //       call obviously will have node_level == level and don't have to
    //       be reregistered. We have to reregister all literals with
    //       node_level > level that are located inbetween the currently
    //       registered ones and previously registered ones with
    //       node_level <= level, which is guaranteed by continuing iteration
    //       from the back until the break point while reregistering literals.
    d_theoryEngine->preRegister(node);
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
