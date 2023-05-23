/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for managing the contexts
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__CONTEXT_MANAGER_H
#define CVC5__SMT__CONTEXT_MANAGER_H

#include <vector>

#include "context/context.h"
#include "smt/env_obj.h"
#include "smt/smt_mode.h"
#include "util/result.h"
#include "util/synth_result.h"

namespace cvc5::internal {
namespace smt {

class SmtDriver;
class SolverEngineState;

/**
 * This class manages how the SAT and user contexts should be used in
 * cooperation with the SmtSolver.
 */
class ContextManager : protected EnvObj
{
 public:
  ContextManager(Env& env, SolverEngineState& state);
  ~ContextManager() {}
  /**
   * Notify that we are resetting the assertions, called when a reset-assertions
   * command is issued by the user.
   */
  void notifyResetAssertions();
  /**
   * Notify that we are about to call check-sat. This call is made prior to
   * initializing the assertions. It processes pending pops and pushes a
   * (user) context if necessary.
   *
   * @param hasAssumptions Whether the call to check-sat has assumptions. If
   * so, we push a context.
   */
  void notifyCheckSat(bool hasAssumptions);
  /**
   * Notify that the result of the last check-sat was r. This should be called
   * once immediately following notifyCheckSat() if the check-sat call
   * returned normal (i.e. it was not interrupted).
   *
   * @param hasAssumptions Whether the prior call to check-sat had assumptions.
   * If so, we pop a context.
   */
  void notifyCheckSatResult(bool hasAssumptions);
  /**
   * Setup the context, which makes a single push to maintain a global
   * context around everything.
   *
   * @param smt The driver that handles notifications from this context
   * manager
   */
  void setup(SmtDriver* smt);
  /**
   * Prepare for a shutdown of the SolverEngine, which does pending pops and
   * pops the user context to zero.
   */
  void shutdown();
  /**
   * Cleanup, which pops all contexts to level zero.
   */
  void cleanup();

  //---------------------------- context management
  /**
   * Do all pending pops, which ensures that the context levels are up-to-date.
   * This method should be called by the SolverEngine before using any of its
   * members that rely on the context (e.g. PropEngine or TheoryEngine).
   */
  void doPendingPops();
  /**
   * Called when the user of SolverEngine issues a push. This corresponds to
   * the SMT-LIB command push.
   */
  void userPush();
  /**
   * Called when the user of SolverEngine issues a pop. This corresponds to
   * the SMT-LIB command pop.
   */
  void userPop();
  //---------------------------- end context management

  //---------------------------- queries
  /** Return the user context level.  */
  size_t getNumUserLevels() const;
  //---------------------------- end queries

 private:
  /** Pushes the user and SAT contexts */
  void push();
  /** Pops the user and SAT contexts */
  void pop();
  /** Pops the user and SAT contexts to the given level */
  void popto(uint32_t toLevel);
  /**
   * Internal push, which processes any pending pops, and pushes (if in
   * incremental mode).
   */
  void internalPush();
  /**
   * Internal pop. If immediate is true, this processes any pending pops, and
   * pops (if in incremental mode). Otherwise, it increments the pending pop
   * counter and does nothing.
   */
  void internalPop(bool immediate = false);
  /** Reference to the SolverEngineState */
  SolverEngineState& d_state;
  /** Pointer to the SmtDriver */
  SmtDriver* d_smt;
  /** The context levels of user pushes */
  std::vector<uint32_t> d_userLevels;
  /** Number of internal pops that have been deferred. */
  unsigned d_pendingPops;
  /**
   * Internal status flag to indicate whether we have been issued a
   * notifyCheckSat call and have yet to process the "postsolve" methods of
   * SolverEngine via SolverEngine::notifyPostSolve().
   */
  bool d_needPostsolve;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
