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
  switch (d_objectiveCombination)
  {
    case BOX: return optimizeBox(); break;
    case LEXICOGRAPHIC: return optimizeLexicographicIterative(); break;
    case PARETO: return optimizeParetoNaiveGIA(); break;
    default: CVC5_FATAL() << "Unknown objective combination";
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
  // kills the optChecker created by pareto
  d_optChecker.reset();
  d_optChecker = createOptCheckerWithTimeout(d_parent);
  OptimizationResult partialResult;
  OptimizationResult::ResultType totalResultType = OptimizationResult::OPTIMAL;
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
        if (totalResultType == OptimizationResult::OPTIMAL)
        {
          totalResultType = OptimizationResult::UNSAT;
        }
        break;
      case OptimizationResult::UNKNOWN:
        totalResultType = OptimizationResult::UNKNOWN;
        break;
      default: Unreachable();
    }

    d_results[i] = partialResult;
  }
  // kill optChecker in case pareto misuses it
  d_optChecker.reset();
  return totalResultType;
}

OptimizationResult::ResultType
OptimizationSolver::optimizeLexicographicIterative()
{
  // kills the optChecker created by pareto
  d_optChecker.reset();
  d_optChecker = createOptCheckerWithTimeout(d_parent);
  OptimizationResult partialResult;
  OptimizationResult::ResultType totalResultType = OptimizationResult::OPTIMAL;
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

    d_results[i] = partialResult;

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
  return totalResultType;
}

OptimizationResult::ResultType OptimizationSolver::optimizeParetoNaiveGIA()
{
  if (!d_optChecker) d_optChecker = createOptCheckerWithTimeout(d_parent);
  NodeManager* nm = d_optChecker->getNodeManager();

  Result satResult = d_optChecker->checkSat();

  switch (satResult.isSat())
  {
    case Result::Sat::UNSAT: return OptimizationResult::UNSAT;
    case Result::Sat::SAT_UNKNOWN: return OptimizationResult::UNKNOWN;
    case Result::Sat::SAT:
    {
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


  std::vector<Node> noWorseObj;
  std::vector<Node> someObjBetter;
  d_optChecker->push();

  while (satResult.isSat() == Result::Sat::SAT)
  {
    noWorseObj.clear();
    someObjBetter.clear();

    for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
    {
      noWorseObj.push_back(
          OMTOptimizer::mkWeakIncrementalExpression(nm,
                                                    d_objectives[i].getTarget(),
                                                    d_results[i].getValue(),
                                                    d_objectives[i]));
      someObjBetter.push_back(OMTOptimizer::mkStrongIncrementalExpression(
          nm,
          d_objectives[i].getTarget(),
          d_results[i].getValue(),
          d_objectives[i]));
      // noWorseObj.push_back(nm->mkNode(kind::BITVECTOR_UGE, d_objectives[i].getTarget(), d_results[i].getValue()));
      // someObjBetter.push_back(nm->mkNode(kind::BITVECTOR_UGT, d_objectives[i].getTarget(), d_results[i].getValue()));
    }
    d_optChecker->assertFormula(nm->mkAnd(noWorseObj));
    d_optChecker->assertFormula(nm->mkOr(someObjBetter));

    satResult = d_optChecker->checkSat();

    switch (satResult.isSat())
    {
      case Result::Sat::UNSAT: break;
      case Result::Sat::SAT_UNKNOWN:
        d_optChecker.reset();
        return OptimizationResult::UNKNOWN;
      case Result::Sat::SAT:
      {
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

  // before we return!
  // please do assert that some objective could be better
  // in order to break the ties for the next run!!!
  d_optChecker->assertFormula(nm->mkOr(someObjBetter));

  return OptimizationResult::OPTIMAL;
}

}  // namespace smt
}  // namespace cvc5
