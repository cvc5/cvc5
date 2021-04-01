/*********************                                                        */
/*! \file optimization_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Michael Chang, Yancheng Ou
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for optimization queries
 **/

#include "smt/optimization_solver.h"

#include "omt/omt_optimizer.h"

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

OptimizationSolver::OptimizationSolver(SmtEngine* parent)
    : d_parent(parent),
      d_activatedObjective(Node(), ObjectiveType::OBJECTIVE_UNDEFINED),
      d_savedValue()
{
}

OptimizationSolver::~OptimizationSolver() {}

OptResult OptimizationSolver::checkOpt()
{
  // Make sure that the objective is not the default one
  Assert(d_activatedObjective.getType() != ObjectiveType::OBJECTIVE_UNDEFINED);
  Assert(!d_activatedObjective.getNode().isNull());

  std::unique_ptr<OMTOptimizer> optimizer = OMTOptimizer::getOptimizerForNode(
      d_activatedObjective.getNode(), d_activatedObjective.getSigned());

  Assert(optimizer != nullptr);

  std::pair<OptResult, Node> optResult;
  if (d_activatedObjective.getType() == ObjectiveType::OBJECTIVE_MAXIMIZE)
  {
    optResult = optimizer->maximize(this->d_parent,
                                    this->d_activatedObjective.getNode());
  }
  else if (d_activatedObjective.getType() == ObjectiveType::OBJECTIVE_MINIMIZE)
  {
    optResult = optimizer->minimize(this->d_parent,
                                    this->d_activatedObjective.getNode());
  }

  this->d_savedValue = optResult.second;
  return optResult.first;
}

void OptimizationSolver::activateObj(const Node& obj,
                                     const ObjectiveType type,
                                     bool bvSigned)
{
  d_activatedObjective = Objective(obj, type, bvSigned);
}

Node OptimizationSolver::objectiveGetValue()
{
  Assert(!d_savedValue.isNull());
  return d_savedValue;
}

Objective::Objective(Node obj, ObjectiveType type, bool bvSigned)
    : d_type(type), d_node(obj), d_bvSigned(bvSigned)
{
}

ObjectiveType Objective::getType() { return d_type; }

Node Objective::getNode() { return d_node; }

bool Objective::getSigned() { return d_bvSigned; }

}  // namespace smt
}  // namespace cvc5
