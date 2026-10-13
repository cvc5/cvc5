/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_DRIVER_H
#define CVC5__SMT__SMT_DRIVER_H

#include <vector>

#include "context/cdo.h"
#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "smt/illegal_checker.h"
#include "util/result.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class ContextManager;

/**
 * SMT driver class.
 *
 * The purpose of this class is to define algorithms for checking
 * satisfiability beyond a single call to the underlying SMT solver. The
 * default implementation, SmtDriverSingleCall, is used for invoking a
 * single call to the SMT solver only.
 */
class SmtDriver : protected EnvObj
{
 public:
  SmtDriver(Env& env, SmtSolver& smt, ContextManager* ctx);
  virtual ~SmtDriver() {}
  /**
   * Check satisfiability. This invokes the algorithm given by this driver
   * for checking satisfiability.
   *
   * @param assumptions The assumptions for this check-sat call, which are
   * temporary assertions.
   */
  Result checkSat(const std::vector<Node>& assumptions);

  /**
   * Refresh the assertions that have been asserted to the underlying SMT
   * solver. This gets the set of unprocessed assertions of the underlying
   * SMT solver, preprocesses them, pushes them into the SMT solver.
   *
   * We ensure that assertions are refreshed eagerly during user pushes to
   * ensure that assertions are only preprocessed in one context.
   */
  void refreshAssertions();
  // --------------------------------------- callbacks from the context manager
  /**
   * Notify push pre, which is called just before the user context of the state
   * pushes. This processes all pending assertions.
   */
  void notifyPushPre();
  /**
   * Notify push post, which is called just after the user context of the state
   * pushes. This performs a push on the underlying prop engine.
   */
  void notifyPushPost();
  /**
   * Notify pop pre, which is called just before the user context of the state
   * pops. This performs a pop on the underlying prop engine.
   */
  void notifyPopPre();
  /**
   * Notify post solve, which is called once per check-sat query. It is
   * triggered when the first d_state.doPendingPops() is issued after the
   * check-sat. This calls the postsolve method of the underlying TheoryEngine.
   */
  void notifyPostSolve();
  // ----------------------------------- end callbacks from the context manager
 protected:
  /**
   * Get the next assertions, store in ap. Refreshes the SMT solver's
   * assertions and calls the driver-specific getNextAssertions method.
   */
  void getNextAssertionsInternal(preprocessing::AssertionPipeline& ap);
  /**
   * Check satisfiability next, return the result.
   *
   * If the result is unknown with UnknownExplanation REQUIRES_CHECK_AGAIN,
   * then this driver will be called to getNextAssertions as described below
   * and another call to checkSatNext will be made.
   *
   * Otherwise, the returned result is the final one returned by the
   * checkSatisfiability method above.
   */
  virtual Result checkSatNext(preprocessing::AssertionPipeline& ap) = 0;
  /**
   * Called at the beginning of every call to checkSat, before any assertions
   * are consumed. Drivers that consume assertions incrementally use this to
   * remember their state, so that it can be restored by notifyResourceOut.
   */
  virtual void notifyCheckSatStart() {}
  /**
   * Called when a check-sat call was aborted by a ResourceOutException. The
   * assertions that were obtained by this call were not (fully) processed, so
   * drivers that consume assertions incrementally must make them available to
   * the next call again.
   */
  virtual void notifyResourceOut() {}
  /**
   * Get the next assertions. This is called:
   * (1) immediately before calls to checkSatNext, where we populate ap with
   * those that will be checked on the next call to checkSatNext.
   * (2) in calls to refreshAssertions, where we populate ap with all
   * assertions that require being pushed to the SAT solver.
   */
  virtual void getNextAssertions(preprocessing::AssertionPipeline& ap) = 0;
  /** The underlying SMT solver */
  SmtSolver& d_smt;
  /**
   * The underlying context manager. This is only required to be provided
   * if the checkSatNext method ever sets checkAgain to true.
   */
  ContextManager* d_ctx;
  /** assertions pipeline */
  preprocessing::AssertionPipeline d_ap;
  /**
   * The utility used for checking for illegal inputs
   */
  IllegalChecker d_illegalChecker;
  /**
   * Set (in the user context) when a check-sat call was aborted by a
   * ResourceOutException, either at the top level or in a frame that absorbed
   * it. Such an abort may leave partially processed state behind in the user
   * context (e.g. a cached skolem whose definition was never sent, or a
   * literal whose clauses were never added to the SAT solver). This state only
   * lacks constraints, thus "unsat" answers remain correct but "sat" answers
   * may not be. While this flag is set, "sat" is not reported. It is reset when
   * the user context is popped below the level where the abort happened.
   */
  context::CDO<bool> d_resourceOutTaint;
};

/**
 * The default SMT driver, which makes a single call to the underlying
 * SMT solver.
 *
 * Notice this class does not require ContextManager if we are not doing
 * incremental solving with this driver.
 */
class SmtDriverSingleCall : public SmtDriver
{
 public:
  SmtDriverSingleCall(Env& env, SmtSolver& smt, ContextManager* ctx = nullptr);
  virtual ~SmtDriverSingleCall() {}

 protected:
  /** Check sat next, takes result of underlying SMT solver only */
  Result checkSatNext(preprocessing::AssertionPipeline& ap) override;
  /** Gets all the assertions we have yet to process */
  void getNextAssertions(preprocessing::AssertionPipeline& ap) override;
  /** Remember the value of d_assertionListIndex */
  void notifyCheckSatStart() override;
  /** Restore the value of d_assertionListIndex */
  void notifyResourceOut() override;
  /**
   * The first index in the assertion list of the underlying SMT solver that we
   * have not processed yet. The call to getNextAssertions gets all assertions
   * starting from this index onward.
   */
  context::CDO<size_t> d_assertionListIndex;
  /**
   * The value of d_assertionListIndex when the current call to checkSat
   * started.
   */
  size_t d_assertionListIndexAtStart;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
