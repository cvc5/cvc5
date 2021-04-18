/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Michael Chang
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

std::pair<OptResult, Node> OMTOptimizerInteger::optimize(SmtEngine* optChecker,
                                                         Node target,
                                                         ObjectiveType objType)
{
  NodeManager* nm = optChecker->getNodeManager();

  Result intermediateSatResult = optChecker->checkSat();
  // Model-value of objective (used in optimization loop)
  Node value;
  if (intermediateSatResult.isUnknown())
  {
    return std::make_pair(OptResult::OPT_UNKNOWN, value);
  }
  if (intermediateSatResult.isSat() == Result::UNSAT)
  {
    return std::make_pair(OptResult::OPT_UNSAT, value);
  }
  // asserts objective > old_value (used in optimization loop)
  Node increment;
  Kind incrementalOperator = kind::NULL_EXPR;
  if (objType == ObjectiveType::OBJECTIVE_MINIMIZE)
  {
    // if objective is MIN, then assert optimization_target <
    // current_model_value
    incrementalOperator = kind::LT;
  }
  else if (objType == ObjectiveType::OBJECTIVE_MAXIMIZE)
  {
    // if objective is MAX, then assert optimization_target >
    // current_model_value
    incrementalOperator = kind::GT;
  }

  value = optChecker->getValue(target);
  Assert(!value.isNull());

  // Workhorse of linear search:
  // This loop will keep incrmenting/decrementing the objective until unsat
  // When unsat is hit,
  // the optimized value is the model value just before the unsat call
  while (intermediateSatResult.isSat() == Result::SAT)
  {
    increment = nm->mkNode(incrementalOperator, target, value);
    // push before making further assertions
    optChecker->push();
    optChecker->assertFormula(increment);
    intermediateSatResult = optChecker->checkSat();
    if (intermediateSatResult.isSat() == Result::SAT)
    {
      value = optChecker->getValue(target);
      Assert(!value.isNull());
    }
    // pop the assertion
    optChecker->pop();
  }

  return std::make_pair(OptResult::OPT_OPTIMAL, value);
}

std::pair<OptResult, Node> OMTOptimizerInteger::minimize(SmtEngine* optChecker,
                                                         Node target)
{
  return this->optimize(optChecker, target, ObjectiveType::OBJECTIVE_MINIMIZE);
}
std::pair<OptResult, Node> OMTOptimizerInteger::maximize(SmtEngine* optChecker,
                                                         Node target)
{
  return this->optimize(optChecker, target, ObjectiveType::OBJECTIVE_MAXIMIZE);
}

}  // namespace cvc5::omt
