/******************************************************************************
 * Top contributors (to current version):
 *   Michael Chang, Yancheng Ou, Aina Niemetz
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

OptimizationResult::ResultType OptimizationSolver::checkOpt()
{
  Assert(d_objectives.size() == 1);
  // NOTE: currently we are only dealing with single obj
  std::unique_ptr<OMTOptimizer> optimizer =
      OMTOptimizer::getOptimizerForObjective(d_objectives[0]);

  if (!optimizer) return OptimizationResult::UNSUPPORTED;

  OptimizationResult optResult;
  std::unique_ptr<SmtEngine> optChecker = createOptCheckerWithTimeout(d_parent);
  if (d_objectives[0].getType() == OptimizationObjective::MAXIMIZE)
  {
    optResult =
        optimizer->maximize(optChecker.get(), d_objectives[0].getTarget());
  }
  else if (d_objectives[0].getType() == OptimizationObjective::MINIMIZE)
  {
    optResult =
        optimizer->minimize(optChecker.get(), d_objectives[0].getTarget());
  }

  d_results[0] = optResult;
  return optResult.getType();
}

void OptimizationSolver::pushObjective(
    TNode target, OptimizationObjective::ObjectiveType type, bool bvSigned)
{
  d_objectives.emplace_back(target, type, bvSigned);
  d_results.emplace_back(OptimizationResult::UNSUPPORTED, Node());
}

void OptimizationSolver::popObjective()
{
  d_objectives.pop_back();
  d_results.pop_back();
}

std::vector<OptimizationResult> OptimizationSolver::getValues()
{
  Assert(d_objectives.size() == d_results.size());
  return d_results;
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

}  // namespace smt
}  // namespace cvc5
