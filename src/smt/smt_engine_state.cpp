/*********************                                                        */
/*! \file smt_engine_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for maintaining the state of the SMT engine.
 **/

#include "smt/smt_engine_state.h"

#include "options/smt_options.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace smt {

SmtEngineState::SmtEngineState(SmtEngine& smt)
    : d_smt(smt),
      d_context(new context::Context()),
      d_userContext(new context::UserContext()),
      d_pendingPops(0),
      d_fullyInited(false),
      d_queryMade(false),
      d_needPostsolve(false),
      d_status(),
      d_expectedStatus(),
      d_smtMode(SmtMode::START)
{
}

void SmtEngineState::notifyExpectedStatus(const std::string& status)
{
  Assert(status == "sat" || status == "unsat" || status == "unknown")
      << "SmtEngineState::notifyExpectedStatus: unexpected status string "
      << status;
  d_expectedStatus = Result(status, d_filename);
}

void SmtEngineState::notifyResetAssertions()
{
  doPendingPops();
  while (!d_userLevels.empty())
  {
    userPop();
  }
  // Remember the global push/pop around everything when beyond Start mode
  // (see solver execution modes in the SMT-LIB standard)
  Assert(d_userLevels.size() == 0 && d_userContext->getLevel() == 1);
  popto(0);
}

void SmtEngineState::notifyCheckSat(bool hasAssumptions)
{
  // process the pending pops
  doPendingPops();
  if (d_queryMade && !options::incrementalSolving())
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

void SmtEngineState::notifyCheckSatResult(bool hasAssumptions, Result r)
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
    CVC4_FATAL() << "Expected result " << d_expectedStatus << " but got "
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

void SmtEngineState::notifyGetAbduct(bool success)
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

void SmtEngineState::notifyGetInterpol(bool success)
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

void SmtEngineState::setup()
{
  // push a context
  push();
}

void SmtEngineState::finishInit()
{
  // set the flag to remember that we are fully initialized
  d_fullyInited = true;
}

void SmtEngineState::shutdown()
{
  doPendingPops();

  while (options::incrementalSolving() && d_userContext->getLevel() > 1)
  {
    internalPop(true);
  }
}

void SmtEngineState::cleanup()
{
  // pop to level zero
  popto(0);
}

void SmtEngineState::setFilename(const std::string& filename)
{
  d_filename = filename;
}

void SmtEngineState::userPush()
{
  if (!options::incrementalSolving())
  {
    throw ModalException(
        "Cannot push when not solving incrementally (use --incremental)");
  }
  // The problem isn't really "extended" yet, but this disallows
  // get-model after a push, simplifying our lives somewhat and
  // staying symmetric with pop.
  d_smtMode = SmtMode::ASSERT;

  d_userLevels.push_back(d_userContext->getLevel());
  internalPush();
  Trace("userpushpop") << "SmtEngineState: pushed to level "
                       << d_userContext->getLevel() << std::endl;
}

void SmtEngineState::userPop()
{
  if (!options::incrementalSolving())
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

  AlwaysAssert(d_userContext->getLevel() > 0);
  AlwaysAssert(d_userLevels.back() < d_userContext->getLevel());
  while (d_userLevels.back() < d_userContext->getLevel())
  {
    internalPop(true);
  }
  d_userLevels.pop_back();
}

void SmtEngineState::push()
{
  d_userContext->push();
  d_context->push();
}

void SmtEngineState::pop()
{
  d_userContext->pop();
  d_context->pop();
}

void SmtEngineState::popto(int toLevel)
{
  d_context->popto(toLevel);
  d_userContext->popto(toLevel);
}

context::UserContext* SmtEngineState::getUserContext()
{
  return d_userContext.get();
}

context::Context* SmtEngineState::getContext() { return d_context.get(); }

Result SmtEngineState::getStatus() const { return d_status; }

bool SmtEngineState::isFullyInited() const { return d_fullyInited; }
bool SmtEngineState::isFullyReady() const
{
  return d_fullyInited && d_pendingPops == 0;
}
bool SmtEngineState::isQueryMade() const { return d_queryMade; }
size_t SmtEngineState::getNumUserLevels() const { return d_userLevels.size(); }

SmtMode SmtEngineState::getMode() const { return d_smtMode; }

const std::string& SmtEngineState::getFilename() const { return d_filename; }

void SmtEngineState::internalPush()
{
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngineState::internalPush()" << std::endl;
  doPendingPops();
  if (options::incrementalSolving())
  {
    // notifies the SmtEngine to process the assertions immediately
    d_smt.notifyPushPre();
    d_userContext->push();
    // the context push is done inside of the SAT solver
    d_smt.notifyPushPost();
  }
}

void SmtEngineState::internalPop(bool immediate)
{
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngineState::internalPop()" << std::endl;
  if (options::incrementalSolving())
  {
    ++d_pendingPops;
  }
  if (immediate)
  {
    doPendingPops();
  }
}

void SmtEngineState::doPendingPops()
{
  Trace("smt") << "SmtEngineState::doPendingPops()" << std::endl;
  Assert(d_pendingPops == 0 || options::incrementalSolving());
  // check to see if a postsolve() is pending
  if (d_needPostsolve)
  {
    d_smt.notifyPostSolvePre();
  }
  while (d_pendingPops > 0)
  {
    // the context pop is done inside of the SAT solver
    d_smt.notifyPopPre();
    // pop the context
    d_userContext->pop();
    --d_pendingPops;
    // no need for pop post (for now)
  }
  if (d_needPostsolve)
  {
    d_smt.notifyPostSolvePost();
    d_needPostsolve = false;
  }
}

}  // namespace smt
}  // namespace CVC4
