/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Ying Sheng
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

#include "cvc5_private.h"

#ifndef CVC5__SMT__CONTEXT_MANAGER_H
#define CVC5__SMT__CONTEXT_MANAGER_H

#include <string>

#include "context/context.h"
#include "smt/env_obj.h"
#include "smt/smt_mode.h"
#include "util/result.h"
#include "util/synth_result.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class SolverEngineState;

/**
 * This utility is responsible for maintaining the basic state of the
 * SolverEngine.
 *
 * It has no concept of anything related to the assertions of the SolverEngine,
 * or more generally it does not depend on Node.
 *
 * This class has three sets of interfaces:
 * (1) notification methods that are used by SolverEngine to notify when an
 * event occurs (e.g. the beginning of a check-sat call), (2) maintaining the
 * SAT and user contexts to be used by the SolverEngine, (3) general information
 * queries, including the mode that the SolverEngine is in, based on the
 * notifications it has received.
 *
 * It maintains a reference to the SolverEngine for the sake of making
 * callbacks.
 */
class ContextManager : protected EnvObj
{
 public:
  ContextManager(Env& env, SolverEngineState& state, SmtSolver& smt);
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
   * returned normal (i.e. it was not interupted).
   *
   * @param hasAssumptions Whether the prior call to check-sat had assumptions.
   * If so, we pop a context.
   */
  void notifyCheckSatResult(bool hasAssumptions);
  /**
   * Setup the context, which makes a single push to maintain a global
   * context around everything.
   */
  void setup();
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
  void popto(int toLevel);
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
  /** Reference to the SmtSolver */
  SmtSolver& d_smt;
  /** The context levels of user pushes */
  std::vector<int> d_userLevels;

  /**
   * Number of internal pops that have been deferred.
   */
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
