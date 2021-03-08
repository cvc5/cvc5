/*********************                                                        */
/*! \file optimization_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Michael Chang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for optimization queries
 **/

#include "smt/optimization_solver.h"

#include "options/smt_options.h"
#include "smt/smt_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/smt_engine_subsolver.h"

using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

/**
 * d_activatedObjective is initialized to a default objective:
 * default objective constructed with Null Node and OBJECTIVE_UNDEFINED
 *
 * d_savedValue is initialized to a default node (Null Node)
 */

OptimizationSolver::OptimizationSolver(SmtEngine* parent)
    : d_parent(parent),
      d_activatedObjective(Node(), OBJECTIVE_UNDEFINED),
      d_savedValue()
{
}

OptimizationSolver::~OptimizationSolver() {}

OptResult OptimizationSolver::checkOpt()
{
  // Make sure that the objective is not the default one
  Assert(d_activatedObjective.getType() != OBJECTIVE_UNDEFINED);
  Assert(!d_activatedObjective.getNode().isNull());

  // the smt engine to which we send intermediate queries
  // for the linear search.
  std::unique_ptr<SmtEngine> optChecker;
  initializeSubsolver(optChecker);
  NodeManager* nm = optChecker->getNodeManager();

  // we need to be in incremental mode for multiple objectives since we need to
  // push pop we need to produce models to inrement on our objective
  optChecker->setOption("incremental", "true");
  optChecker->setOption("produce-models", "true");

  // Move assertions from the parent solver to the subsolver
  std::vector<Node> p_assertions = d_parent->getExpandedAssertions();
  for (const Node& e : p_assertions)
  {
    optChecker->assertFormula(e);
  }

  // We need to checksat once before the optimization loop so we have a
  // baseline value to increment
  Result loop_r = optChecker->checkSat();

  if (loop_r.isUnknown())
  {
    return OPT_UNKNOWN;
  }
  if (!loop_r.isSat())
  {
    return OPT_UNSAT;
  }

  // Model-value of objective (used in optimization loop)
  Node value;
  // asserts objective > old_value (used in optimization loop)
  Node increment;

  // Workhorse of linear optimization:
  // This loop will keep incrmenting the objective until unsat
  // When unsat is hit, the optimized value is the model value just before the
  // unsat call
  while (loop_r.isSat())
  {
    // get the model-value of objective in last sat call
    value = optChecker->getValue(d_activatedObjective.getNode());

    // We need to save the value since we need the model value just before the
    // unsat call
    Assert(!value.isNull());
    d_savedValue = value;

    // increment on the model-value of objective:
    // if we're maximizing increment = objective > old_objective value
    // if we're minimizing increment = objective < old_objective value
    if (d_activatedObjective.getType() == OBJECTIVE_MAXIMIZE)
    {
      increment = nm->mkNode(kind::GT, d_activatedObjective.getNode(), value);
    }
    else
    {
      increment = nm->mkNode(kind::LT, d_activatedObjective.getNode(), value);
    }
    optChecker->assertFormula(increment);
    loop_r = optChecker->checkSat();
  }

  return OPT_OPTIMAL;
}

void OptimizationSolver::activateObj(const Node& obj, const int& type)
{
  d_activatedObjective = Objective(obj, (ObjectiveType)type);
}

Node OptimizationSolver::objectiveGetValue()
{
  Assert(!d_savedValue.isNull());
  return d_savedValue;
}

Objective::Objective(Node obj, ObjectiveType type) : d_type(type), d_node(obj)
{
}

ObjectiveType Objective::getType() { return d_type; }

Node Objective::getNode() { return d_node; }

}  // namespace smt
}  // namespace CVC4
