/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Michael Chang, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for optimization queries.
 */

#include "smt/optimization_solver.h"

#include "omt/omt_optimizer.h"
#include "options/smt_options.h"
#include "smt/assertions.h"
#include "smt/smt_engine.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::theory;
using namespace cvc5::omt;
namespace cvc5 {
namespace smt {

OptimizationSolver::OptimizationSolver(SmtEngine* parent)
    : d_parent(parent),
      d_optChecker(),
      d_objectives(),
      d_results(),
      d_objectiveCombination(BOX)
{
}

OptimizationResult::ResultType OptimizationSolver::checkOpt()
{
  switch (d_objectiveCombination)
  {
    case BOX: return optimizeBox(); break;
    default: Unimplemented() << "Objective combination not-yet implemented";
  }
  Unreachable();
}

bool OptimizationSolver::pushObjective(
    TNode target, OptimizationObjective::ObjectiveType type, bool bvSigned)
{
  if (!OMTOptimizer::nodeSupportsOptimization(target))
  {
    Warning()
        << "Objective not pushed: Target node does not support optimization";
    return false;
  }
  d_optChecker.reset();
  d_objectives.emplace_back(target, type, bvSigned);
  d_results.emplace_back(OptimizationResult::UNKNOWN, Node());
  return true;
}

void OptimizationSolver::popObjective()
{
  d_optChecker.reset();
  d_objectives.pop_back();
  d_results.pop_back();
}

std::vector<OptimizationResult> OptimizationSolver::getValues()
{
  Assert(d_objectives.size() == d_results.size());
  return d_results;
}

void OptimizationSolver::setObjectiveCombination(
    ObjectiveCombination combination)
{
  d_objectiveCombination = combination;
  d_optChecker.reset();
}

std::unique_ptr<SmtEngine> OptimizationSolver::createOptCheckerWithTimeout(
    SmtEngine* parentSMTSolver, bool needsTimeout, unsigned long timeout)
{
  std::unique_ptr<SmtEngine> optChecker;
  // initializeSubSolver will copy the options and theories enabled
  // from the current solver to optChecker and adds timeout
  theory::initializeSubsolver(optChecker, needsTimeout, timeout);
  // we need to be in incremental mode for multiple objectives since we need to
  // push pop we need to produce models to inrement on our objective
  optChecker->setOption("incremental", "true");
  optChecker->setOption("produce-models", "true");
  // Move assertions from the parent solver to the subsolver
  std::vector<Node> p_assertions = parentSMTSolver->getExpandedAssertions();
  for (const Node& e : p_assertions)
  {
    optChecker->assertFormula(e);
  }
  return optChecker;
}

OptimizationResult::ResultType OptimizationSolver::optimizeBox()
{
  // clears the optChecker
  d_optChecker.reset();
  d_optChecker = createOptCheckerWithTimeout(d_parent);
  OptimizationResult partialResult;
  OptimizationResult::ResultType aggregatedResultType =
      OptimizationResult::OPTIMAL;
  std::unique_ptr<OMTOptimizer> optimizer;
  for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
  {
    optimizer = OMTOptimizer::getOptimizerForObjective(d_objectives[i]);
    switch (d_objectives[i].getType())
    {
      case OptimizationObjective::MAXIMIZE:
        partialResult = optimizer->maximize(d_optChecker.get(),
                                            d_objectives[i].getTarget());
        break;
      case OptimizationObjective::MINIMIZE:
        partialResult = optimizer->minimize(d_optChecker.get(),
                                            d_objectives[i].getTarget());
        break;
      default:
        CVC5_FATAL()
            << "Optimization objective is neither MAXIMIZE nor MINIMIZE";
    }

    switch (partialResult.getType())
    {
      case OptimizationResult::OPTIMAL: break;
      case OptimizationResult::UNBOUNDED: break;
      case OptimizationResult::UNSAT:
        if (aggregatedResultType == OptimizationResult::OPTIMAL)
        {
          aggregatedResultType = OptimizationResult::UNSAT;
        }
        break;
      case OptimizationResult::UNKNOWN:
        aggregatedResultType = OptimizationResult::UNKNOWN;
        break;
      default: Unreachable();
    }

    d_results[i] = partialResult;
  }
  // kill optChecker after optimization ends
  d_optChecker.reset();
  return aggregatedResultType;
}

}  // namespace smt
}  // namespace cvc5
