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

/**
 * d_activatedObjective is initialized to a default objective:
 * default objective constructed with Null Node and OBJECTIVE_UNDEFINED
 *
 * d_savedValue is initialized to a default node (Null Node)
 */

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

  // creates a blackbox subsolver without timeout
  std::unique_ptr<SmtEngine> optChecker = this->createOptCheckerWithTimeout();

  std::unique_ptr<OMTOptimizer> optimizer;

  std::pair<OptResult, Node> optPartialResult;

  OptResult optResult = OptResult::OPT_UNKNOWN; 

  for (size_t i = 0; i < d_objectives.size(); ++i)
  {
    Objective &obj = d_objectives[i];
    optimizer = OMTOptimizer::getOptimizerForObjective(obj);
    // optimizer is nullptr, meaning that we don't have support for the node type
    if (!optimizer) {
      return OptResult::OPT_UNSUPPORTED;
    }

    ObjectiveType objType = obj.d_type;
    switch (objType)
    {
    case ObjectiveType::OBJECTIVE_MAXIMIZE:
      optPartialResult = optimizer->maximize(optChecker.get(), obj.d_node);
      break;
    case ObjectiveType::OBJECTIVE_MINIMIZE: 
      optPartialResult = optimizer->minimize(optChecker.get(), obj.d_node);
      break;
    default:
      break;
    }

    switch (optPartialResult.first)
    {
    case OptResult::OPT_OPTIMAL :
      // just continue 
      break;
    case OptResult::OPT_UNBOUNDED: 
      break;
    case OptResult::OPT_SAT_APPROX: 
      optResult = OptResult::OPT_SAT_APPROX;
      // also continue 
      break;
    
    case OptResult::OPT_UNSAT: 
      // unsatisfiable target 
      return OptResult::OPT_UNSAT;
    case OptResult::OPT_UNKNOWN: 
      return OptResult::OPT_UNKNOWN;
    default:
      break;
    }

    this->d_optValues[i] = optPartialResult.second;

  }

  return optResult; 
}

void OptimizationSolver::activateObj(Node node,
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

}  // namespace smt
}  // namespace cvc5
