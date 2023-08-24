/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Ying Sheng
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

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_ENGINE_STATE_H
#define CVC5__SMT__SMT_ENGINE_STATE_H

#include <string>

#include "context/context.h"
#include "smt/env_obj.h"
#include "smt/smt_mode.h"
#include "util/result.h"
#include "util/synth_result.h"

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
 * event occurs (e.g. the beginning of a check-sat call), (2) general
 * information queries, including the mode that the SolverEngine is in, based on
 * the notifications it has received.
 */
class SolverEngineState : protected EnvObj
{
 public:
  SolverEngineState(Env& env);
  ~SolverEngineState() {}
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
   * Notify that we are about to call check-sat. This call is made prior to
   * initializing the assertions.
   */
  void notifyCheckSat();
  /**
   * Called when the user of SolverEngine issues a push. This corresponds to
   * the SMT-LIB command push.
   */
  void notifyUserPush();
  /**
   * Called when the user of SolverEngine issues a pop. This corresponds to
   * the SMT-LIB command pop.
   */
  void notifyUserPop();
  /**
   * Notify that the result of the last check-sat was r. This should be called
   * once immediately following notifyCheckSat() if the check-sat call
   * returned normal (i.e. it was not interupted).
   *
   * @param r The result of the check-sat call.
   */
  void notifyCheckSatResult(const Result& r);
  /**
   * Notify that the result of the last check-synth or check-synth-next was r.
   * @param r The result of the check-synth or check-synth-next call.
   */
  void notifyCheckSynthResult(const SynthResult& r);
  /**
   * Notify that we finished an abduction query, where success is whether the
   * command was successful. This is managed independently of the above
   * calls for notifying check-sat. In other words, if a get-abduct command
   * is issued to an SolverEngine, it may use a satisfiability call (if desired)
   * to solve the abduction query. This method is called *in addition* to
   * the above calls to notifyCheckSat / notifyCheckSatResult in this case.
   * In particular, it is called after these two methods are completed.
   * This overwrites the SMT mode to the "ABDUCT" mode if the call to abduction
   * was successful.
   */
  void notifyGetAbduct(bool success);
  /**
   * Notify that we finished an interpolation query, where success is whether
   * the command was successful. This is managed independently of the above
   * calls for notifying check-sat. In other words, if a get-interpolant command
   * is issued to an SolverEngine, it may use a satisfiability call (if desired)
   * to solve the interpolation query. This method is called *in addition* to
   * the above calls to notifyCheckSat / notifyCheckSatResult in this case.
   * In particular, it is called after these two methods are completed.
   * This overwrites the SMT mode to the "INTERPOL" mode if the call to
   * interpolation was successful.
   */
  void notifyGetInterpol(bool success);
  /**
   * Notify that we finished a find-synth or find-synth-next query, where
   * success is whether the command was successful.
   */
  void notifyFindSynth(bool success);
  /**
   * Set that we are in a fully initialized state.
   */
  void markFinishInit();

  //---------------------------- queries
  /**
   * Return true if the SolverEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SolverEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  bool isFullyInited() const;
  /**
   * Return true if a notifyCheckSat call has been made, e.g. a query has been
   * issued to the SolverEngine.
   */
  bool isQueryMade() const;
  /** Get the status of the last check-sat */
  Result getStatus() const;
  /** Get the SMT mode we are in */
  SmtMode getMode() const;
  //---------------------------- end queries

 private:
  /**
   * Whether or not the SolverEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SolverEngine which calls the finishInit method above; e.g. when
   * the first formula is asserted, a call to simplify() is issued, a scope is
   * pushed, etc.
   */
  bool d_fullyInited;

  /**
   * Whether or not a notifyCheckSat call has been made, which corresponds to
   * when a checkSatisfiability() has already been
   * made through the SolverEngine.  If true, and incrementalSolving is false,
   * then attempting an additional checks for satisfiability will fail with
   * a ModalException during notifyCheckSat.
   */
  bool d_queryMade;
  /**
   * Most recent result of last checkSatisfiability in the
   * SolverEngine.
   */
  Result d_status;

  /**
   * The expected status of the next satisfiability check.
   */
  Result d_expectedStatus;

  /** The SMT mode, for details see enumeration above. */
  SmtMode d_smtMode;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
