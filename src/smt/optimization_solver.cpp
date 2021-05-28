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
      d_objectiveCombination(LEXICOGRAPHIC)
{
}

OptimizationResult::ResultType OptimizationSolver::checkOpt()
{
  for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
  {
    // reset the optimization results
    d_results[i] = OptimizationResult();
  }
  switch (d_objectiveCombination)
  {
    case BOX: return optimizeBox(); break;
    case LEXICOGRAPHIC: return optimizeLexicographicIterative(); break;
    case PARETO: return optimizeParetoNaiveGIA(); break;
    default:
      CVC5_FATAL()
          << "Unknown objective combination, "
          << "valid objective combinations are BOX, LEXICOGRAPHIC and PARETO";
  }
  Unreachable();
}

void OptimizationSolver::addObjective(TNode target,
                                      OptimizationObjective::ObjectiveType type,
                                      bool bvSigned)
{
  if (!OMTOptimizer::nodeSupportsOptimization(target))
  {
    CVC5_FATAL()
        << "Objective failed to add: Target node does not support optimization";
  }
  d_optChecker.reset();
  d_objectives.emplace_back(target, type, bvSigned);
  d_results.emplace_back(OptimizationResult::UNKNOWN, Node());
}

void OptimizationSolver::resetObjectives()
{
  d_optChecker.reset();
  d_objectives.clear();
  d_results.clear();
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
  // resets the optChecker
  d_optChecker = createOptCheckerWithTimeout(d_parent);
  OptimizationResult partialResult;
  OptimizationResult::ResultType aggregatedResultType =
      OptimizationResult::OPTIMAL;
  std::unique_ptr<OMTOptimizer> optimizer;
  for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
  {
    optimizer = OMTOptimizer::getOptimizerForObjective(d_objectives[i]);
    // checks whether the objective type is maximize or minimize
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
    // match the optimization result type, and aggregate the results of
    // subproblems
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

OptimizationResult::ResultType
OptimizationSolver::optimizeLexicographicIterative()
{
  // resets the optChecker
  d_optChecker = createOptCheckerWithTimeout(d_parent);
  OptimizationResult partialResult;
  std::unique_ptr<OMTOptimizer> optimizer;
  for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
  {
    optimizer = OMTOptimizer::getOptimizerForObjective(d_objectives[i]);
    // checks if the objective is maximize or minimize
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

    d_results[i] = partialResult;

    // checks the optimization result of the current objective
    switch (partialResult.getType())
    {
      case OptimizationResult::OPTIMAL:
        // assert target[i] == value[i] and proceed
        d_optChecker->assertFormula(d_optChecker->getNodeManager()->mkNode(
            kind::EQUAL, d_objectives[i].getTarget(), d_results[i].getValue()));
        break;
      case OptimizationResult::UNBOUNDED: return OptimizationResult::UNBOUNDED;
      case OptimizationResult::UNSAT: return OptimizationResult::UNSAT;
      case OptimizationResult::UNKNOWN: return OptimizationResult::UNKNOWN;
      default: Unreachable();
    }
  }
  // kill optChecker in case pareto misuses it
  d_optChecker.reset();
  // now all objectives are OPTIMAL, just return OPTIMAL as overall result
  return OptimizationResult::OPTIMAL;
}

OptimizationResult::ResultType OptimizationSolver::optimizeParetoNaiveGIA()
{
  // initial call to Pareto optimizer, create the checker
  if (!d_optChecker) d_optChecker = createOptCheckerWithTimeout(d_parent);
  NodeManager* nm = d_optChecker->getNodeManager();

  // checks whether the current set of assertions are satisfied or not
  Result satResult = d_optChecker->checkSat();

  switch (satResult.isSat())
  {
    case Result::Sat::UNSAT: return OptimizationResult::UNSAT;
    case Result::Sat::SAT_UNKNOWN: return OptimizationResult::UNKNOWN;
    case Result::Sat::SAT:
    {
      // if satisfied, use d_results to store the initial results
      // they will be gradually updated and optimized
      // until no more optimal value could be found
      for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
      {
        d_results[i] = OptimizationResult(
            OptimizationResult::OPTIMAL,
            d_optChecker->getValue(d_objectives[i].getTarget()));
      }
      break;
    }
    default: Unreachable();
  }

  // a vector storing assertions saying that no objective is worse
  std::vector<Node> noWorseObj;
  // a vector storing assertions saying that there is at least one objective
  // that could be improved
  std::vector<Node> someObjBetter;
  d_optChecker->push();

  while (satResult.isSat() == Result::Sat::SAT)
  {
    noWorseObj.clear();
    someObjBetter.clear();

    for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
    {
      // for maximize value[i] <= obj[i],
      // for minimize obj[i] <= value[i]
      noWorseObj.push_back(
          OMTOptimizer::mkWeakIncrementalExpression(nm,
                                                    d_objectives[i].getTarget(),
                                                    d_results[i].getValue(),
                                                    d_objectives[i]));
      // for maximize value[i] < obj[i],
      // for minimize obj[i] < value[i]
      someObjBetter.push_back(OMTOptimizer::mkStrongIncrementalExpression(
          nm,
          d_objectives[i].getTarget(),
          d_results[i].getValue(),
          d_objectives[i]));
    }
    d_optChecker->assertFormula(nm->mkAnd(noWorseObj));
    d_optChecker->assertFormula(nm->mkOr(someObjBetter));
    // checks if previous assertions + noWorseObj + someObjBetter are satisfied
    satResult = d_optChecker->checkSat();

    switch (satResult.isSat())
    {
      case Result::Sat::UNSAT:
        // if result is UNSAT, it means no more improvement could be made,
        // then the results stored in d_results are one of the Pareto optimal
        // results
        break;
      case Result::Sat::SAT_UNKNOWN:
        // if result is UNKNOWN, abort the current session and return UNKNOWN
        d_optChecker.reset();
        return OptimizationResult::UNKNOWN;
      case Result::Sat::SAT:
      {
        // if result is SAT, update d_results to the more optimal values
        for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
        {
          d_results[i] = OptimizationResult(
              OptimizationResult::OPTIMAL,
              d_optChecker->getValue(d_objectives[i].getTarget()));
        }
        break;
      }
      default: Unreachable();
    }
  }

  d_optChecker->pop();

  // before we return:
  // assert that some objective could be better
  // in order not to get the same optimal solution
  // for the next run.
  d_optChecker->assertFormula(nm->mkOr(someObjBetter));

  return OptimizationResult::OPTIMAL;
}

}  // namespace smt
}  // namespace cvc5
