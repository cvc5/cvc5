/*********************                                                        */
/*! \file smt_engine_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for maintaining the state of the SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__SMT_ENGINE_STATE_H
#define CVC4__SMT__SMT_ENGINE_STATE_H

#include <string>

#include "context/context.h"
#include "smt/smt_mode.h"
#include "util/result.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * This utility is responsible for maintaining the basic state of the SmtEngine.
 *
 * It has no concept of anything related to the assertions of the SmtEngine,
 * or more generally it does not depend on Node.
 *
 * This class has three sets of interfaces:
 * (1) notification methods that are used by SmtEngine to notify when an event
 * occurs (e.g. the beginning of a check-sat call),
 * (2) maintaining the SAT and user contexts to be used by the SmtEngine,
 * (3) general information queries, including the mode that the SmtEngine is
 * in, based on the notifications it has received.
 *
 * It maintains a reference to the SmtEngine for the sake of making callbacks.
 */
class SmtEngineState
{
 public:
  SmtEngineState(SmtEngine& smt);
  ~SmtEngineState() {}
  /**
   * Notify that the expected status of the next check-sat is given by the
   * string status, which should be one of "sat", "unsat" or "unknown".
   */
  void notifyExpectedStatus(const std::string& status);
  /**
   * Notify that the SmtEngine is fully initialized, which is called when
   * options are finalized.
   */
  void notifyFullyInited();
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
   * @param r The result of the check-sat call.
   */
  void notifyCheckSatResult(bool hasAssumptions, Result r);
  /**
   * Notify that we finished an abduction query, where success is whether the
   * command was successful. This is managed independently of the above
   * calls for notifying check-sat. In other words, if a get-abduct command
   * is issued to an SmtEngine, it may use a satisfiability call (if desired)
   * to solve the abduction query. This method is called *in addition* to
   * the above calls to notifyCheckSat / notifyCheckSatResult in this case.
   * In particular, it is called after these two methods are completed.
   * This overwrites the SMT mode to the "ABDUCT" mode if the call to abduction
   * was successful.
   */
  void notifyGetAbduct(bool success);
  /**
   * Setup the context, which makes a single push to maintain a global
   * context around everything.
   */
  void setup();
  /**
   * Set that we are in a fully initialized state.
   */
  void finishInit();
  /**
   * Prepare for a shutdown of the SmtEngine, which does pending pops and
   * pops the user context to zero.
   */
  void shutdown();
  /**
   * Cleanup, which pops all contexts to level zero.
   */
  void cleanup();
  /**
   * Set that the file name of the current instance is the given string. This
   * is used for various purposes (e.g. get-info, SZS status).
   */
  void setFilename(const std::string& filename);

  //---------------------------- context management
  /**
   * Do all pending pops, which ensures that the context levels are up-to-date.
   * This method should be called by the SmtEngine before using any of its
   * members that rely on the context (e.g. PropEngine or TheoryEngine).
   */
  void doPendingPops();
  /**
   * Called when the user of SmtEngine issues a push. This corresponds to
   * the SMT-LIB command push.
   */
  void userPush();
  /**
   * Called when the user of SmtEngine issues a pop. This corresponds to
   * the SMT-LIB command pop.
   */
  void userPop();
  /** Get a pointer to the UserContext owned by this SmtEngine. */
  context::UserContext* getUserContext();
  /** Get a pointer to the Context owned by this SmtEngine. */
  context::Context* getContext();
  //---------------------------- end context management

  //---------------------------- queries
  /**
   * Return true if the SmtEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SmtEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  bool isFullyInited() const;
  /**
   * Return true if the SmtEngine is fully initialized and there are no
   * pending pops.
   */
  bool isFullyReady() const;
  /**
   * Return true if a notifyCheckSat call has been made, e.g. a query has been
   * issued to the SmtEngine.
   */
  bool isQueryMade() const;
  /** Return the user context level.  */
  size_t getNumUserLevels() const;
  /** Get the status of the last check-sat */
  Result getStatus() const;
  /** Get the SMT mode we are in */
  SmtMode getMode() const;
  /** return the input name (if any) */
  const std::string& getFilename() const;
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
  /** Reference to the SmtEngine */
  SmtEngine& d_smt;
  /** Expr manager context */
  std::unique_ptr<context::Context> d_context;
  /** User level context */
  std::unique_ptr<context::UserContext> d_userContext;
  /** The context levels of user pushes */
  std::vector<int> d_userLevels;

  /**
   * Number of internal pops that have been deferred.
   */
  unsigned d_pendingPops;

  /**
   * Whether or not the SmtEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SmtEngine which calls the finishInit method above; e.g. when
   * the first formula is asserted, a call to simplify() is issued, a scope is
   * pushed, etc.
   */
  bool d_fullyInited;

  /**
   * Whether or not a notifyCheckSat call has been made, which corresponds to
   * when a checkEntailed() or checkSatisfiability() has already been
   * made through the SmtEngine.  If true, and incrementalSolving is false,
   * then attempting an additional checks for satisfiability will fail with
   * a ModalException during notifyCheckSat.
   */
  bool d_queryMade;

  /**
   * Internal status flag to indicate whether we have been issued a
   * notifyCheckSat call and have yet to process the "postsolve" methods of
   * SmtEngine via SmtEngine::notifyPostSolvePre/notifyPostSolvePost.
   */
  bool d_needPostsolve;

  /**
   * Most recent result of last checkSatisfiability/checkEntailed in the
   * SmtEngine.
   */
  Result d_status;

  /**
   * The expected status of the next satisfiability check.
   */
  Result d_expectedStatus;

  /** The SMT mode, for details see enumeration above. */
  SmtMode d_smtMode;

  /**
   * The input file name or the name set through (set-info :filename ...), if
   * any.
   */
  std::string d_filename;
};

}  // namespace smt
}  // namespace CVC4

#endif
