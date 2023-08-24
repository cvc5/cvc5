/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace smt {

SolverEngineState::SolverEngineState(Env& env)
    : EnvObj(env),
      d_fullyInited(false),
      d_queryMade(false),
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
  Assert(d_expectedStatus.getStatus() != Result::NONE);
}
void SolverEngineState::notifyCheckSat()
{
  // process the pending pops
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
}

void SolverEngineState::notifyCheckSatResult(const Result& r)
{
  // Remember the status
  d_status = r;
  // Check against expected status, if it is set
  if (d_expectedStatus.getStatus() != Result::NONE)
  {
    // unknown results don't give an error
    if (!d_expectedStatus.isUnknown() && !d_status.isUnknown()
        && d_status != d_expectedStatus)
    {
      CVC5_FATAL() << "Expected result " << d_expectedStatus << " but got "
                   << d_status;
    }
  }
  // clear expected status
  d_expectedStatus = Result();
  // Update the SMT mode
  switch (d_status.getStatus())
  {
    case Result::UNSAT: d_smtMode = SmtMode::UNSAT; break;
    case Result::SAT: d_smtMode = SmtMode::SAT; break;
    default: d_smtMode = SmtMode::SAT_UNKNOWN;
  }
}

void SolverEngineState::notifyCheckSynthResult(const SynthResult& r)
{
  if (r.getStatus() == SynthResult::SOLUTION)
  {
    // successfully generated a synthesis solution, update to synth state
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

void SolverEngineState::notifyFindSynth(bool success)
{
  if (success)
  {
    d_smtMode = SmtMode::FIND_SYNTH;
  }
  else
  {
    // failed, we revert to the assert state
    d_smtMode = SmtMode::ASSERT;
  }
}

void SolverEngineState::markFinishInit()
{
  // set the flag to remember that we are fully initialized
  d_fullyInited = true;
}

void SolverEngineState::notifyUserPush()
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
}

void SolverEngineState::notifyUserPop()
{
  if (!options().base.incrementalSolving)
  {
    throw ModalException(
        "Cannot pop when not solving incrementally (use --incremental)");
  }
  // The problem isn't really "extended" yet, but this disallows
  // get-model after a pop, simplifying our lives somewhat.  It might
  // not be strictly necessary to do so, since the pops occur lazily,
  // but also it would be weird to have a legally-executed (get-model)
  // that only returns a subset of the assignment (because the rest
  // is no longer in scope!).
  d_smtMode = SmtMode::ASSERT;
}

Result SolverEngineState::getStatus() const { return d_status; }

bool SolverEngineState::isFullyInited() const { return d_fullyInited; }

bool SolverEngineState::isQueryMade() const { return d_queryMade; }

SmtMode SolverEngineState::getMode() const { return d_smtMode; }

}  // namespace smt
}  // namespace cvc5::internal
