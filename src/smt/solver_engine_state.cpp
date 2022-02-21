/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Ying Sheng
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for maintaining the state of the SMT engine.
 */

#include "smt/solver_engine_state.h"

#include "base/modal_exception.h"
#include "options/base_options.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/solver_engine.h"

namespace cvc5 {
namespace smt {

SolverEngineState::SolverEngineState(Env& env, SolverEngine& slv)
    : EnvObj(env),
      d_slv(slv),
      d_pendingPops(0),
      d_fullyInited(false),
      d_queryMade(false),
      d_needPostsolve(false),
      d_status(),
      d_expectedStatus(),
      d_smtMode(SmtMode::START)
{
}

void SolverEngineState::notifyExpectedStatus(const std::string& status)
{
  Assert(status == "sat" || status == "unsat" || status == "unknown")
      << "SolverEngineState::notifyExpectedStatus: unexpected status string "
      << status;
  d_expectedStatus = Result(status, options().driver.filename);
}

void SolverEngineState::notifyResetAssertions()
{
  doPendingPops();
  while (!d_userLevels.empty())
  {
    userPop();
  }
  // Remember the global push/pop around everything when beyond Start mode
  // (see solver execution modes in the SMT-LIB standard)
  Assert(d_userLevels.size() == 0 && userContext()->getLevel() == 1);
  popto(0);
}

void SolverEngineState::notifyCheckSat(bool hasAssumptions)
{
  // process the pending pops
  doPendingPops();
  if (d_queryMade && !options().base.incrementalSolving)
  {
    throw ModalException(
        "Cannot make multiple queries unless "
        "incremental solving is enabled "
        "(try --incremental)");
  }

  // Note that a query has been made and we are in assert mode
  d_queryMade = true;
  d_smtMode = SmtMode::ASSERT;

  // push if there are assumptions
  if (hasAssumptions)
  {
    internalPush();
  }
}

void SolverEngineState::notifyCheckSatResult(bool hasAssumptions, Result r)
{
  d_needPostsolve = true;

  // Pop the context
  if (hasAssumptions)
  {
    internalPop();
  }

  // Remember the status
  d_status = r;
  // Check against expected status
  if (!d_expectedStatus.isUnknown() && !d_status.isUnknown()
      && d_status != d_expectedStatus)
  {
    CVC5_FATAL() << "Expected result " << d_expectedStatus << " but got "
                 << d_status;
  }
  // clear expected status
  d_expectedStatus = Result();
  // Update the SMT mode
  switch (d_status.asSatisfiabilityResult().isSat())
  {
    case Result::UNSAT: d_smtMode = SmtMode::UNSAT; break;
    case Result::SAT: d_smtMode = SmtMode::SAT; break;
    default: d_smtMode = SmtMode::SAT_UNKNOWN;
  }
}

void SolverEngineState::notifyCheckSynthResult(Result r)
{
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    // successfully generated a synthesis solution, update to abduct state
    d_smtMode = SmtMode::SYNTH;
  }
  else
  {
    // failed, we revert to the assert state
    d_smtMode = SmtMode::ASSERT;
  }
}

void SolverEngineState::notifyGetAbduct(bool success)
{
  if (success)
  {
    // successfully generated an abduct, update to abduct state
    d_smtMode = SmtMode::ABDUCT;
  }
  else
  {
    // failed, we revert to the assert state
    d_smtMode = SmtMode::ASSERT;
  }
}

void SolverEngineState::notifyGetInterpol(bool success)
{
  if (success)
  {
    // successfully generated an interpolant, update to interpol state
    d_smtMode = SmtMode::INTERPOL;
  }
  else
  {
    // failed, we revert to the assert state
    d_smtMode = SmtMode::ASSERT;
  }
}

void SolverEngineState::setup()
{
  // push a context
  push();
}

void SolverEngineState::finishInit()
{
  // set the flag to remember that we are fully initialized
  d_fullyInited = true;
}

void SolverEngineState::shutdown()
{
  doPendingPops();

  while (options().base.incrementalSolving && userContext()->getLevel() > 1)
  {
    internalPop(true);
  }
}

void SolverEngineState::cleanup()
{
  // pop to level zero
  popto(0);
}

void SolverEngineState::userPush()
{
  if (!options().base.incrementalSolving)
  {
    throw ModalException(
        "Cannot push when not solving incrementally (use --incremental)");
  }
  // The problem isn't really "extended" yet, but this disallows
  // get-model after a push, simplifying our lives somewhat and
  // staying symmetric with pop.
  d_smtMode = SmtMode::ASSERT;

  d_userLevels.push_back(userContext()->getLevel());
  internalPush();
  Trace("userpushpop") << "SolverEngineState: pushed to level "
                       << userContext()->getLevel() << std::endl;
}

void SolverEngineState::userPop()
{
  if (!options().base.incrementalSolving)
  {
    throw ModalException(
        "Cannot pop when not solving incrementally (use --incremental)");
  }
  if (d_userLevels.size() == 0)
  {
    throw ModalException("Cannot pop beyond the first user frame");
  }
  // The problem isn't really "extended" yet, but this disallows
  // get-model after a pop, simplifying our lives somewhat.  It might
  // not be strictly necessary to do so, since the pops occur lazily,
  // but also it would be weird to have a legally-executed (get-model)
  // that only returns a subset of the assignment (because the rest
  // is no longer in scope!).
  d_smtMode = SmtMode::ASSERT;

  AlwaysAssert(userContext()->getLevel() > 0);
  AlwaysAssert(d_userLevels.back() < userContext()->getLevel());
  while (d_userLevels.back() < userContext()->getLevel())
  {
    internalPop(true);
  }
  d_userLevels.pop_back();
}
void SolverEngineState::push()
{
  userContext()->push();
  context()->push();
}

void SolverEngineState::pop()
{
  userContext()->pop();
  context()->pop();
}

void SolverEngineState::popto(int toLevel)
{
  context()->popto(toLevel);
  userContext()->popto(toLevel);
}

Result SolverEngineState::getStatus() const { return d_status; }

bool SolverEngineState::isFullyInited() const { return d_fullyInited; }
bool SolverEngineState::isFullyReady() const
{
  return d_fullyInited && d_pendingPops == 0;
}
bool SolverEngineState::isQueryMade() const { return d_queryMade; }
size_t SolverEngineState::getNumUserLevels() const
{
  return d_userLevels.size();
}

SmtMode SolverEngineState::getMode() const { return d_smtMode; }

void SolverEngineState::internalPush()
{
  Assert(d_fullyInited);
  Trace("smt") << "SolverEngineState::internalPush()" << std::endl;
  doPendingPops();
  if (options().base.incrementalSolving)
  {
    // notifies the SolverEngine to process the assertions immediately
    d_slv.notifyPushPre();
    userContext()->push();
    // the context push is done inside of the SAT solver
    d_slv.notifyPushPost();
  }
}

void SolverEngineState::internalPop(bool immediate)
{
  Assert(d_fullyInited);
  Trace("smt") << "SolverEngineState::internalPop()" << std::endl;
  if (options().base.incrementalSolving)
  {
    ++d_pendingPops;
  }
  if (immediate)
  {
    doPendingPops();
  }
}

void SolverEngineState::doPendingPops()
{
  Trace("smt") << "SolverEngineState::doPendingPops()" << std::endl;
  Assert(d_pendingPops == 0 || options().base.incrementalSolving);
  // check to see if a postsolve() is pending
  if (d_needPostsolve)
  {
    d_slv.notifyPostSolvePre();
  }
  while (d_pendingPops > 0)
  {
    // the context pop is done inside of the SAT solver
    d_slv.notifyPopPre();
    // pop the context
    userContext()->pop();
    --d_pendingPops;
    // no need for pop post (for now)
  }
  if (d_needPostsolve)
  {
    d_slv.notifyPostSolvePost();
    d_needPostsolve = false;
  }
}

}  // namespace smt
}  // namespace cvc5
