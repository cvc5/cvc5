/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SMT queries in an SolverEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_DRIVER_DEEP_RESTARTS_H
#define CVC5__SMT__SMT_DRIVER_DEEP_RESTARTS_H

#include "smt/smt_driver.h"
#include "util/result.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class ContextManager;

/**
 * An SMT driver that is based on deep restarts.
 *
 * The idea of this SMT driver is to call the SMT solver with all assertions
 * with learned literal tracking enabled, and where it terminates with
 * "unknown" if:
 * - at least one literal has been learned, and
 * - no literal has been learned after some threshold.
 * In this case, we preprocess and checkSat again where the SMT solver has
 * its PropEngine and TheoryEngine reset.
 */
class SmtDriverDeepRestarts : public SmtDriver
{
 public:
  SmtDriverDeepRestarts(Env& env, SmtSolver& smt, ContextManager* ctx);
  virtual ~SmtDriverDeepRestarts(){}

 protected:
  Result checkSatNext(preprocessing::AssertionPipeline& ap) override;
  void getNextAssertions(preprocessing::AssertionPipeline& ap) override;

 private:
  /** first time? */
  bool d_firstTime;
  /** The current learned literals */
  std::vector<Node> d_zll;
  /** All learned literals, used for debugging */
  std::unordered_set<Node> d_allLearnedLits;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
