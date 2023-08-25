/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Andrew Reynolds, Michael Chang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

using namespace cvc5::internal::theory;
using namespace cvc5::internal::omt;
namespace cvc5::internal {
namespace smt {

std::ostream& operator<<(std::ostream& out, const OptimizationResult& result)
{
  // check the output language first
  Language lang = options::ioutils::getOutputLanguage(out);
  if (!language::isLangSmt2(lang))
  {
    Unimplemented()
        << "Only the SMTLib2 language supports optimization right now";
  }
  out << "(" << result.getResult();
  switch (result.getResult().getStatus())
  {
    case Result::SAT:
    case Result::UNKNOWN:
    {
      switch (result.isInfinity())
      {
        case OptimizationResult::FINITE:
          out << "\t" << result.getValue();
          break;
        case OptimizationResult::POSTITIVE_INF: out << "\t+Inf"; break;
        case OptimizationResult::NEGATIVE_INF: out << "\t-Inf"; break;
        default: break;
      }
      break;
    }
    case Result::UNSAT: break;
    default: Unreachable();
  }
  out << ")";
  return out;
}

std::ostream& operator<<(std::ostream& out,
                         const OptimizationObjective& objective)
{
  // check the output language first
  Language lang = options::ioutils::getOutputLanguage(out);
  if (!language::isLangSmt2(lang))
  {
    Unimplemented()
        << "Only the SMTLib2 language supports optimization right now";
  }
  out << "(";
  switch (objective.getType())
  {
    case OptimizationObjective::MAXIMIZE: out << "maximize "; break;
    case OptimizationObjective::MINIMIZE: out << "minimize "; break;
    default: Unreachable();
  }
  TNode target = objective.getTarget();
  TypeNode type = target.getType();
  out << target;
  if (type.isBitVector())
  {
    out << (objective.bvIsSigned() ? " :signed" : " :unsigned");
  }
  out << ")";
  return out;
}

OptimizationSolver::OptimizationSolver(SolverEngine* parent)
    : EnvObj(parent->getEnv()),
      d_parent(parent),
      d_optChecker(),
      d_objectives(userContext()),
      d_results()
{
}

Result OptimizationSolver::checkOpt(ObjectiveCombination combination)
{
  // if the results of the previous call have different size than the
  // objectives, then we should clear the pareto optimization context
  if (d_results.size() != d_objectives.size()) d_optChecker.reset();
  // initialize the result vector
  d_results.clear();
  for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
  {
    d_results.emplace_back();
  }
  switch (combination)
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
}

std::vector<OptimizationResult> OptimizationSolver::getValues()
{
  return d_results;
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
  std::vector<Node> p_assertions = parentSMTSolver->getSubstitutedAssertions();
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
  Result aggregatedResult(Result::SAT);
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
    switch (partialResult.getResult().getStatus())
    {
      case Result::SAT: break;
      case Result::UNSAT:
        // the assertions are unsatisfiable
        for (size_t j = 0; j < numObj; ++j)
        {
          d_results[j] = partialResult;
        }
        d_optChecker.reset();
        return partialResult.getResult();
      case Result::UNKNOWN: aggregatedResult = partialResult.getResult(); break;
      default: Unreachable();
    }

    d_results[i] = partialResult;
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
    switch (partialResult.getResult().getStatus())
    {
      case Result::SAT:
        // assert target[i] == value[i] and proceed
        d_optChecker->assertFormula(NodeManager::currentNM()->mkNode(
            kind::EQUAL, d_objectives[i].getTarget(), d_results[i].getValue()));
        break;
      case Result::UNSAT:
        d_optChecker.reset();
        return partialResult.getResult();
      case Result::UNKNOWN:
        d_optChecker.reset();
        return partialResult.getResult();
      default: Unreachable();
    }

    // if the result for the current objective is unbounded
    // (result is not finite) then just stop
    if (partialResult.isInfinity() != OptimizationResult::FINITE) break;
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
  NodeManager* nm = NodeManager::currentNM();

  // checks whether the current set of assertions are satisfied or not
  Result satResult = d_optChecker->checkSat();

  switch (satResult.getStatus())
  {
    case Result::UNSAT:
    case Result::UNKNOWN: return satResult;
    case Result::SAT:
    {
      // if satisfied, use d_results to store the initial results
      // they will be gradually updated and optimized
      // until no more optimal value could be found
      for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
      {
        d_results[i] = OptimizationResult(
            satResult, d_optChecker->getValue(d_objectives[i].getTarget()));
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

  while (satResult.getStatus() == Result::SAT)
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

    switch (satResult.getStatus())
    {
      case Result::UNSAT:
        // if result is UNSAT, it means no more improvement could be made,
        // then the results stored in d_results are one of the Pareto optimal
        // results
        break;
      case Result::UNKNOWN:
        // if result is UNKNOWN, abort the current session and return UNKNOWN
        d_optChecker.reset();
        return satResult;
      case Result::SAT:
      {
        lastSatResult = satResult;
        // if result is SAT, update d_results to the more optimal values
        for (size_t i = 0, numObj = d_objectives.size(); i < numObj; ++i)
        {
          d_results[i] = OptimizationResult(
              satResult, d_optChecker->getValue(d_objectives[i].getTarget()));
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
}  // namespace cvc5::internal
