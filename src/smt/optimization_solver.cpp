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
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::theory;
using namespace cvc5::omt;
namespace cvc5 {
namespace smt {

OptimizationSolver::OptimizationSolver(SmtEngine* parent,
                                       ObjectiveOrder objOrder)
    : d_parent(parent), d_objectives(), d_optValues(), d_objOrder(objOrder)
{
}

OptResult OptimizationSolver::checkOpt()
{
  // Make sure that the objective is not the default one
  Assert(!d_objectives.empty());
  for (Objective& obj : d_objectives)
  {
    Assert(!obj.d_node.isNull());
    Assert(obj.d_type != ObjectiveType::OBJECTIVE_UNDEFINED);
  }
  switch (this->d_objOrder)
  {
    case ObjectiveOrder::OBJORDER_BOX: return this->optimizeBox();
    case ObjectiveOrder::OBJORDER_LEXICOGRAPHIC: return this->optimizeLex();
    case ObjectiveOrder::OBJORDER_PARETO: return this->optimizePareto();
    default: return OptResult::OPT_UNKNOWN;
  }
}

void OptimizationSolver::pushObj(Node node,
                                 ObjectiveType objType,
                                 bool bvSigned)
{
  d_objectives.push_back({node, objType, bvSigned});
  // also creates a placeholder for optValue
  d_optValues.emplace_back();
}

std::vector<Node> OptimizationSolver::objectiveGetValues()
{
  Assert(d_optValues.size() == d_objectives.size());
  return d_optValues;
}

void OptimizationSolver::setObjectiveOrder(ObjectiveOrder newObjOrder)
{
  this->d_objOrder = newObjOrder;
}

std::unique_ptr<SmtEngine> OptimizationSolver::createOptCheckerWithTimeout(
    bool needsTimeout, unsigned long timeout)
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
  std::vector<Node> p_assertions = this->d_parent->getExpandedAssertions();
  for (const Node& e : p_assertions)
  {
    optChecker->assertFormula(e);
  }
  return optChecker;
}

OptResult OptimizationSolver::optimizeBox()
{
  // creates a blackbox subsolver without timeout
  std::unique_ptr<SmtEngine> optChecker = this->createOptCheckerWithTimeout();

  // the dedicated optimizer
  std::unique_ptr<OMTOptimizer> optimizer;

  // temporal result for single goal
  std::pair<OptResult, Node> optPartialResult;

  // optimize for each objective independently
  for (size_t i = 0; i < d_objectives.size(); ++i)
  {
    Objective& obj = d_objectives[i];
    optimizer = OMTOptimizer::getOptimizerForObjective(obj);
    // optimizer is nullptr, meaning that we don't have support for the node
    // type
    if (!optimizer)
    {
      return OptResult::OPT_UNSUPPORTED;
    }

    // notice there's no push and pop around the calls to maximize and minimize!
    // so we require optimizer->maximize and optimizer->minimize to be
    // re-enterable!
    ObjectiveType objType = obj.d_type;
    switch (objType)
    {
      case ObjectiveType::OBJECTIVE_MAXIMIZE:
        optPartialResult = optimizer->maximize(optChecker.get(), obj.d_node);
        break;
      case ObjectiveType::OBJECTIVE_MINIMIZE:
        optPartialResult = optimizer->minimize(optChecker.get(), obj.d_node);
        break;
      default: break;
    }

    switch (optPartialResult.first)
    {
      case OptResult::OPT_OPTIMAL: break;
      // for unbounded goal:
      // the infinity values should be encoded in NodeValue, not in OptResult
      case OptResult::OPT_UNSAT: return OptResult::OPT_UNSAT;
      case OptResult::OPT_UNKNOWN: return OptResult::OPT_UNKNOWN;
      default: break;
    }

    this->d_optValues[i] = optPartialResult.second;
  }

  return OptResult::OPT_OPTIMAL;
}

OptResult OptimizationSolver::optimizeLex()
{
  return OptResult::OPT_UNSUPPORTED;
}

OptResult OptimizationSolver::optimizePareto()
{
  return OptResult::OPT_UNSUPPORTED;
}

}  // namespace smt
}  // namespace cvc5
