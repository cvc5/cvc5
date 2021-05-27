/******************************************************************************
 * Top contributors (to current version):
 *   Michael Chang, Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Optimizer for Integer type.
 */

#include "omt/integer_optimizer.h"

#include "options/smt_options.h"
#include "smt/smt_engine.h"

using namespace cvc5::smt;
namespace cvc5::omt {

OptimizationResult OMTOptimizerInteger::optimize(SmtEngine* optChecker,
                                                 TNode target,
                                                 bool isMinimize)
{
  // linear search for integer goal
  // the smt engine to which we send intermediate queries
  // for the linear search.
  NodeManager* nm = optChecker->getNodeManager();
  optChecker->push();
  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown())
  {
    return OptimizationResult(OptimizationResult::UNKNOWN, value);
  }
  if (intermediateSatResult.isSat() == Result::UNSAT)
  {
    return OptimizationResult(OptimizationResult::UNSAT, value);
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
  // Workhorse of linear search:
  // This loop will keep incrmenting/decrementing the objective until unsat
  // When unsat is hit,
  // the optimized value is the model value just before the unsat call
  while (intermediateSatResult.isSat() == Result::SAT)
  {
    value = optChecker->getValue(target);
    Assert(!value.isNull());
    increment = nm->mkNode(incrementalOperator, target, value);
    optChecker->assertFormula(increment);
    intermediateSatResult = optChecker->checkSat();
  }
  optChecker->pop();
  return OptimizationResult(OptimizationResult::OPTIMAL, value);
}

OptimizationResult OMTOptimizerInteger::minimize(SmtEngine* optChecker,
                                                 TNode target)
{
  return this->optimize(optChecker, target, true);
}
OptimizationResult OMTOptimizerInteger::maximize(SmtEngine* optChecker,
                                                 TNode target)
{
  return this->optimize(optChecker, target, false);
}

}  // namespace cvc5::omt
