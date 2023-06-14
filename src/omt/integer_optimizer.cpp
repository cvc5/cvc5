/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Michael Chang, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Optimizer for Integer type.
 */

#include "omt/integer_optimizer.h"

#include "options/smt_options.h"
#include "smt/solver_engine.h"

using namespace cvc5::internal::smt;
namespace cvc5::internal::omt {

OptimizationResult OMTOptimizerInteger::optimize(SolverEngine* optChecker,
                                                 TNode target,
                                                 bool isMinimize)
{
  // linear search for integer goal
  // the smt engine to which we send intermediate queries
  // for the linear search.
  NodeManager* nm = NodeManager::currentNM();
  optChecker->push();
  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown()
      || intermediateSatResult.getStatus() == Result::UNSAT)
  {
    return OptimizationResult(intermediateSatResult, value);
  }
  // node storing target > old_value (used in optimization loop)
  Node increment;
  Kind incrementalOperator = kind::NULL_EXPR;
  if (isMinimize)
  {
    // if objective is minimize,
    // then assert optimization_target < current_model_value
    incrementalOperator = kind::LT;
  }
  else
  {
    // if objective is maximize,
    // then assert optimization_target > current_model_value
    incrementalOperator = kind::GT;
  }
  Result lastSatResult = intermediateSatResult;
  // Workhorse of linear search:
  // This loop will keep incrmenting/decrementing the objective until unsat
  // When unsat is hit,
  // the optimized value is the model value just before the unsat call
  while (intermediateSatResult.getStatus() == Result::SAT)
  {
    lastSatResult = intermediateSatResult;
    value = optChecker->getValue(target);
    Assert(!value.isNull());
    increment = nm->mkNode(incrementalOperator, target, value);
    optChecker->assertFormula(increment);
    intermediateSatResult = optChecker->checkSat();
  }
  optChecker->pop();
  return OptimizationResult(lastSatResult, value);
}

OptimizationResult OMTOptimizerInteger::minimize(SolverEngine* optChecker,
                                                 TNode target)
{
  return this->optimize(optChecker, target, true);
}
OptimizationResult OMTOptimizerInteger::maximize(SolverEngine* optChecker,
                                                 TNode target)
{
  return this->optimize(optChecker, target, false);
}

}  // namespace cvc5::internal::omt
