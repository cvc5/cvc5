/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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

#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
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
   * Check satisfiability next, return the result.
   *
   * If the result is unknown with UnknownExplanation REQUIRES_CHECK_AGAIN,
   * then this driver will be called to getNextAssertions as described below
   * and another call to checkSatNext will be made.
   *
   * Otherwise, the returned result is the final one returned by the
   * checkSatisfiability method above.
   */
  virtual Result checkSatNext() = 0;
  /**
   * Get the next assertions. This is called immediately after checkSatNext
   * where checkAgain has been set to true. This populates assertions with
   * those that will be checked on the next call to checkSatNext.
   *
   * Note that `as` is always the assertions of the underlying solver d_smt
   * currently.
   */
  virtual void getNextAssertions(Assertions& as) = 0;
  /** The underlying SMT solver */
  SmtSolver& d_smt;
  /**
   * The underlying context manager. This is only required to be provided
   * if the checkSatNext method ever sets checkAgain to true.
   */
  ContextManager* d_ctx;
};

/**
 * The default SMT driver, which makes a single call to the underlying
 * SMT solver.
 *
 * Notice this class does not require ContextManager.
 */
class SmtDriverSingleCall : public SmtDriver
{
 public:
  SmtDriverSingleCall(Env& env, SmtSolver& smt);

 protected:
  /** Check sat next, takes result of underlying SMT solver only */
  Result checkSatNext() override;
  /** Never called */
  void getNextAssertions(Assertions& as) override;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
