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

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "omt/omt_optimizer.h"
#include "options/base_options.h"
#include "options/io_utils.h"
#include "options/language.h"
#include "options/smt_options.h"
#include "smt/assertions.h"
#include "smt/env.h"
#include "smt/solver_engine.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::theory;
using namespace cvc5::omt;
namespace cvc5 {
namespace smt {

OptimizationSolver::OptimizationSolver(SolverEngine* parent)
    : d_parent(parent), d_optChecker(), d_objectives()
{
}

Result OptimizationSolver::checkOpt(ObjectiveCombination combination)
{
  switch (combination)
  {
    case omt::ObjectiveCombination::BOX: return optimizeBox(); break;
    case omt::ObjectiveCombination::LEXICOGRAPHIC:
      return optimizeLexicographicIterative();
      break;
    case omt::ObjectiveCombination::PARETO:
      return optimizeParetoNaiveGIA();
      break;
    default:
      CVC5_FATAL()
          << "Unknown objective combination, "
          << "valid objective combinations are BOX(0), LEXICOGRAPHIC(1) and PARETO(2)";
  }
  Unreachable();
}

void OptimizationSolver::addObjective(TNode target, omt::OptType type)
{
  if (!OMTOptimizer::nodeSupportsOptimization(target))
  {
    CVC5_FATAL()
        << "Objective failed to add: Target node does not support optimization";
  }
  d_optChecker.reset();
  d_objectives.emplace_back(target, type);
  d_targetLookup.insert({target, d_objectives.size() - 1});
}

void OptimizationSolver::clearObjectives()
{
  d_objectives.clear();
  d_targetLookup.clear();
}
bool OptimizationSolver::isOptTarget(TNode n)
{
  return (d_targetLookup.find(n) != d_targetLookup.end());
}
Node OptimizationSolver::getOptValue(TNode target)
{
  auto iter = d_targetLookup.find(target);
  if (iter == d_targetLookup.end())
  {
    return Node();
  }
  return d_objectives[iter->second].getOptResult().getOptimalValue();
}

std::unique_ptr<SolverEngine> OptimizationSolver::createOptCheckerWithTimeout(
    SolverEngine* parentSMTSolver, bool needsTimeout, unsigned long timeout)
{
  std::unique_ptr<SolverEngine> optChecker;
  // initializeSubSolver will copy the options and theories enabled
  // from the current solver to optChecker and adds timeout
  theory::initializeSubsolver(
      optChecker, parentSMTSolver->getEnv(), needsTimeout, timeout);
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

Result OptimizationSolver::optimizeBox()
{
  // resets the optChecker
  d_optChecker = createOptCheckerWithTimeout(d_parent);
  OptimizationResult partialResult;
  Result aggregatedResult(Result::Sat::SAT);
  std::unique_ptr<OMTOptimizer> optimizer;
  for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
  {
    optimizer = OMTOptimizer::getOptimizerForObjective(d_objectives[i]);
    // checks whether the objective type is maximize or minimize
    if (d_objectives[i].isMaximize())
    {
      partialResult =
          optimizer->maximize(d_optChecker.get(), d_objectives[i].getTarget());
    }
    else if (d_objectives[i].isMinimize())
    {
      partialResult =
          optimizer->minimize(d_optChecker.get(), d_objectives[i].getTarget());
    }
    else
    {
      Unreachable();
    }
    // match the optimization result type, and aggregate the results of
    // subproblems
    switch (partialResult.getResult().isSat())
    {
      case Result::SAT: break;
      case Result::UNSAT:
        // the assertions are unsatisfiable
        for (size_t j = 0; j < numObj; ++j)
        {
          d_objectives[j].setOptResult(partialResult);
        }
        d_optChecker.reset();
        return partialResult.getResult();
      case Result::SAT_UNKNOWN:
        aggregatedResult = partialResult.getResult();
        break;
      default: Unreachable();
    }

    d_objectives[i].setOptResult(partialResult);
  }
  // kill optChecker after optimization ends
  d_optChecker.reset();
  return aggregatedResult;
}

Result OptimizationSolver::optimizeLexicographicIterative()
{
  // resets the optChecker
  d_optChecker = createOptCheckerWithTimeout(d_parent);
  // partialResult defaults to SAT if no objective is present
  // NOTE: the parenthesis around Result(Result::SAT) is required,
  // otherwise the compiler will report "parameter declarator cannot be
  // qualified". For more details:
  // https://stackoverflow.com/questions/44045257/c-compiler-error-c2751-what-exactly-causes-it
  // https://en.wikipedia.org/wiki/Most_vexing_parse
  OptimizationResult partialResult((Result(Result::SAT)), TNode());
  std::unique_ptr<OMTOptimizer> optimizer;
  for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
  {
    optimizer = OMTOptimizer::getOptimizerForObjective(d_objectives[i]);
    // checks if the objective is maximize or minimize
    if (d_objectives[i].isMaximize())
    {
      partialResult =
          optimizer->maximize(d_optChecker.get(), d_objectives[i].getTarget());
    }
    else if (d_objectives[i].isMinimize())
    {
      partialResult =
          optimizer->minimize(d_optChecker.get(), d_objectives[i].getTarget());
    }
    else
    {
      Unreachable();
    }

    d_objectives[i].setOptResult(partialResult);

    // checks the optimization result of the current objective
    switch (partialResult.getResult().isSat())
    {
      case Result::SAT:
        // assert target[i] == value[i] and proceed
        d_optChecker->assertFormula(d_optChecker->getNodeManager()->mkNode(
            kind::EQUAL,
            d_objectives[i].getTarget(),
            d_objectives[i].getOptResult().getOptimalValue()));
        break;
      case Result::UNSAT:
        d_optChecker.reset();
        return partialResult.getResult();
      case Result::SAT_UNKNOWN:
        d_optChecker.reset();
        return partialResult.getResult();
      default: Unreachable();
    }

    // if the result for the current objective is unbounded
    // (result is not finite) then just stop
    if (partialResult.isInfinity()) break;
  }
  // kill optChecker in case pareto misuses it
  d_optChecker.reset();
  // now all objectives are optimal, just return SAT as the overall result
  return partialResult.getResult();
}

Result OptimizationSolver::optimizeParetoNaiveGIA()
{
  // initial call to Pareto optimizer, create the checker
  if (!d_optChecker)
  {
    d_optChecker = createOptCheckerWithTimeout(d_parent);
  }
  NodeManager* nm = d_optChecker->getNodeManager();

  // checks whether the current set of assertions are satisfied or not
  Result satResult = d_optChecker->checkSat();

  switch (satResult.isSat())
  {
    case Result::Sat::UNSAT:
    case Result::Sat::SAT_UNKNOWN: return satResult;
    case Result::Sat::SAT:
    {
      // if satisfied, use d_results to store the initial results
      // they will be gradually updated and optimized
      // until no more optimal value could be found
      for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
      {
        d_objectives[i].setOptResult(OptimizationResult(
            satResult, d_optChecker->getValue(d_objectives[i].getTarget())));
      }
      break;
    }
    default: Unreachable();
  }

  Result lastSatResult = satResult;

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
      noWorseObj.push_back(OMTOptimizer::mkWeakIncrementalExpression(
          nm,
          d_objectives[i].getTarget(),
          d_objectives[i].getOptResult().getOptimalValue(),
          d_objectives[i]));
      // for maximize value[i] < obj[i],
      // for minimize obj[i] < value[i]
      someObjBetter.push_back(OMTOptimizer::mkStrongIncrementalExpression(
          nm,
          d_objectives[i].getTarget(),
          d_objectives[i].getOptResult().getOptimalValue(),
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
        return satResult;
      case Result::Sat::SAT:
      {
        lastSatResult = satResult;
        // if result is SAT, update d_results to the more optimal values
        for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
        {
          d_objectives[i].setOptResult(OptimizationResult(
              satResult, d_optChecker->getValue(d_objectives[i].getTarget())));
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

  return lastSatResult;
}

}  // namespace smt
}  // namespace cvc5
