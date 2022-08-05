/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for maintaining the state of the SMT engine.
 */

#include "smt/context_manager.h"

#include "base/modal_exception.h"
#include "options/base_options.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/solver_engine.h"

namespace cvc5::internal {
namespace smt {

ContextManager::ContextManager(Env& env, SolverEngine& slv)
    : EnvObj(env), d_slv(slv), d_pendingPops(0)
{
}
void ContextManager::notifyResetAssertions()
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

void ContextManager::setup()
{
  // push a context
  push();
}

void ContextManager::shutdown()
{
  doPendingPops();

  while (options().base.incrementalSolving && userContext()->getLevel() > 1)
  {
    internalPop(true);
  }
}

void ContextManager::cleanup()
{
  // pop to level zero
  popto(0);
}

void ContextManager::userPush()
{
  if (!options().base.incrementalSolving)
  {
    throw ModalException(
        "Cannot push when not solving incrementally (use --incremental)");
  }

  d_userLevels.push_back(userContext()->getLevel());
  internalPush();
  Trace("userpushpop") << "ContextManager: pushed to level "
                       << userContext()->getLevel() << std::endl;
}

void ContextManager::userPop()
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

  AlwaysAssert(userContext()->getLevel() > 0);
  AlwaysAssert(d_userLevels.back() < userContext()->getLevel());
  while (d_userLevels.back() < userContext()->getLevel())
  {
    internalPop(true);
  }
  d_userLevels.pop_back();
}
void ContextManager::push()
{
  userContext()->push();
  context()->push();
}

void ContextManager::pop()
{
  userContext()->pop();
  context()->pop();
}

void ContextManager::popto(int toLevel)
{
  context()->popto(toLevel);
  userContext()->popto(toLevel);
}
size_t ContextManager::getNumUserLevels() const { return d_userLevels.size(); }

size_t ContextManager::getNumPendingPops() const { return d_pendingPops; }

void ContextManager::internalPush()
{
  // Assert(d_fullyInited);
  Trace("smt") << "ContextManager::internalPush()" << std::endl;
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

void ContextManager::internalPop(bool immediate)
{
  // Assert(d_fullyInited);
  Trace("smt") << "ContextManager::internalPop()" << std::endl;
  if (options().base.incrementalSolving)
  {
    ++d_pendingPops;
  }
  if (immediate)
  {
    doPendingPops();
  }
}

void ContextManager::doPendingPops()
{
  Trace("smt") << "ContextManager::doPendingPops()" << std::endl;
  Assert(d_pendingPops == 0 || options().base.incrementalSolving);
  while (d_pendingPops > 0)
  {
    // the context pop is done inside of the SAT solver
    d_slv.notifyPopPre();
    // pop the context
    userContext()->pop();
    --d_pendingPops;
    // no need for pop post (for now)
  }
}

}  // namespace smt
}  // namespace cvc5::internal
