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

namespace cvc5::internal {

class SolverEngine;

namespace smt {

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
  ContextManager(Env& env, SolverEngine& smt);
  ~ContextManager() {}
  /**
   * Notify that the expected status of the next check-sat is given by the
   * string status, which should be one of "sat", "unsat" or "unknown".
   */
  void notifyExpectedStatus(const std::string& status);
  /**
   * Notify that the SolverEngine is fully initialized, which is called when
   * options are finalized.
   */
  void notifyFullyInited();
  /**
   * Notify that we are resetting the assertions, called when a reset-assertions
   * command is issued by the user.
   */
  void notifyResetAssertions();
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

  /** Return the user context level.  */
  size_t getNumUserLevels() const;
  /** Get the number of pending pops */
  size_t getNumPendingPops() const;

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
  /** Reference to the SolverEngine */
  SolverEngine& d_slv;
  /** The context levels of user pushes */
  std::vector<int> d_userLevels;

  /**
   * Number of internal pops that have been deferred.
   */
  unsigned d_pendingPops;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
