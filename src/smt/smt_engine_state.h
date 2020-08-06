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
#include "util/result.h"

namespace CVC4 {
  
class SmtEngine;

namespace smt {

/**
  * The mode of the solver, which is an extension of Figure 4.1 on
  * page 52 of the SMT-LIB version 2.6 standard
  * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
  */
enum SmtMode
{
  // the initial state of the solver
  SMT_MODE_START,
  // normal state of the solver, after assert/push/pop/declare/define
  SMT_MODE_ASSERT,
  // immediately after a check-sat returning "sat"
  SMT_MODE_SAT,
  // immediately after a check-sat returning "unknown"
  SMT_MODE_SAT_UNKNOWN,
  // immediately after a check-sat returning "unsat"
  SMT_MODE_UNSAT,
  // immediately after a successful call to get-abduct
  SMT_MODE_ABDUCT,
  // immediately after a successful call to get-interpol
  SMT_MODE_INTERPOL
};
  
/**
 * This utility is responsible for maintaining the basic state of the SmtEngine.
 *
 * It has no concept of anything related to the assertions of the SmtEngine,
 * or more generally it does not depend on Node.
 * 
 * Generally speaking, this class has three interfaces:
 * (1) notification methods that are used by SmtEngine to notify when an event
 * occurs (e.g. the beginning of a check-sat call),
 * (2) maintaining the SAT and user contexts to be used by the SmtEngine,
 * (3) querying general information about relevant state information, including
 * the mode that the SmtEngine is in, based on the notifications it has
 * received.
 * 
 * It maintains a reference to the SmtEngine for the sake of making callbacks.
 */
class SmtEngineState
{
 public:
  SmtEngineState(SmtEngine& smt);
  ~SmtEngineState(){}
  
  /**
   * Notify that we are now parsing the input with the given filename.
   * This call sets the filename maintained by this SmtEngine for bookkeeping
   * and also makes a copy of the current options of this SmtEngine. This
   * is required so that the SMT-LIB command (reset) returns the SmtEngine
   * to a state where its options were prior to parsing but after e.g.
   * reading command line options.
   */
  void notifyStartParsing(std::string filename);
  /**
   * Notify that we are resetting the assertions, called when a reset-assertions
   * command is issued by the user.
   */
  void notifyResetAssertions();
  /**
   * Notify that we are about to call check-sat.
   */
  void notifyCheckSat(bool hasAssumptions);
  /**
   * Notify that the result of the last check-sat was r. This should be called
   * once immediately following notifyCheckSat().
   */
  void notifyCheckSatResult(Result r);
  /**
   * Notify that we finished an abduction query, where success is whether the
   * command was successful. This is managed independently of the above
   * calls for notifying check-sat. In other words, if a get-abduct command
   * is issued to an SmtEngine, it may use a satsisfiability call (if desired)
   * to solve the abduction query. This method is called *in addition* to
   * the above calls to notifyCheckSat / notifyCheckSatResult in this case.
   */
  void notifyGetAbduct(bool success);
  /** 
   * Intialize the context, which makes a single push to maintain a global
   * context around everything.
   */
  void initialize();
  /**
   * Prepare for a shutdown of the SmtEngine.
   */
  void shutdown();
  /** Cleanup, which pops the contexts to level 0 */
  void cleanup();
  /**
   * Do all pending pops.
   */
  void doPendingPops();
  
  //---------------------------- context management
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
  /** Get the status of the last check-sat */
  Result getStatus() const;
  /** Get the SMT mode we are in */
  SmtMode getMode() const;
  /** return the input name (if any) */
  std::string getFilename() const;
  //---------------------------- end queries
  
 private:
  /** Pushes the user and SAT contexts */
  void push();
  /** Pops the user and SAT contexts */
  void pop();
  /** Pops the user and SAT contexts to the given level */
  void popto(int toLevel);
  /** Internal push */
  void internalPush();
  /** Internal pop */
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
   * Whether or not this SmtEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SmtEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  bool d_fullyInited;

  /**
   * Whether or not a checkEntailed() or checkSatisfiability() has already been
   * made through this SmtEngine.  If true, and incrementalSolving is false,
   * then attempting an additional checkEntailed() or checkSat() will fail with
   * a ModalException.
   */
  bool d_queryMade;

  /**
   * Internal status flag to indicate whether we've sent a theory
   * presolve() notification and need to match it with a postsolve().
   */
  bool d_needPostsolve;

  /**
   * Most recent result of last checkSatisfiability/checkEntailed or
   * (set-info :status).
   */
  Result d_status;

  /**
   * The expected status of the next satisfiability check.
   */
  Result d_expectedStatus;

  /** The SMT mode, for details see enumeration above. */
  SmtMode d_smtMode;

  /**
   * The input file name (if any) or the name set through setInfo (if any)
   */
  std::string d_filename;
};

}  // namespace smt
}  // namespace CVC4

#endif
