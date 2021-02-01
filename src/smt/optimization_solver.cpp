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

OptimizationSolver::OptimizationSolver(SmtEngine* parent) : d_parent(parent) {}

OptimizationSolver::~OptimizationSolver() {}

bool OptimizationSolver::checkOpt(Result& r)
{
  std::unique_ptr<SmtEngine> optChecker;
  initializeSubsolver(optChecker);
  NodeManager* nm = optChecker->getNodeManager();

  //we need to be in incremental mode for multiple objectives since we need to push pop
  //we need to produce models to inrement on our objective
  optChecker->setOption("incremental", "true");
  optChecker->setOption("produce-models", "true");

  //Move assertions from the parent solver to the subsolver
  std::vector<Node> axioms = d_parent->getExpandedAssertions();
  for (const Node& e : axioms)
  {
    optChecker->assertFormula(e);
  }

  //Loop through all activated objectives and optimize for each
  for (int i = 0; i < d_activatedObjectives.size(); i++)
  {
    optChecker->push();
    Objective o = d_activatedObjectives[i];

    //We need to checksat once before the optimization loop so we have a baseline value to inrement
    r = optChecker->checkSat();

    Result loop_r = r;
    Node value;
    Node increment;

    /*Workhorse of linear optimization:
      This loop will keep incrmenting the objective until unsat
      When unsat is hit, the optimized value is the model value just before the unsat call
    */
    while (loop_r.isSat())
    {
      //get the model-value of objective in last sat call
      value = optChecker->getValue(o.d_node);

      //We need to save the value since we need the model value just before the unsat call
      o.d_savedValue = value;

      /*increment on the model-value of objective:
        if we're maximizing increment = objective > old_objective value
        if we're minimizing increment = objective < old_objective value
      */
      if (o.d_type == OBJECTIVE_MAXIMIZE)
      {
        increment = nm->mkNode(kind::GT, o.d_node, value);
      }
      else
      {
        increment = nm->mkNode(kind::LT, o.d_node, value);
      }
      optChecker->assertFormula(increment);
      loop_r = optChecker->checkSat();
    }

    d_activatedObjectives[i] = o;

    optChecker->pop();
  }

  return true;
}

void OptimizationSolver::activateObj(const Node& obj,
                                     const int& type,
                                     const int& result)
{
  Objective o = Objective(obj, (ObjectiveType)type, (OptResult)result);
  d_activatedObjectives.push_back(o);
}

OptimizationSolver::Objective::Objective(Node obj,
                                         ObjectiveType type,
                                         OptResult result)
    : d_type(type), d_result(OPT_UNKNOWN), d_node(obj), d_savedValue(obj)
{
}

Node OptimizationSolver::objectiveGetValue(const Node& obj)
{
  for (Objective o : d_activatedObjectives)
  {
    if (o.d_node == obj)
    {
      return o.d_savedValue;
    }
  }
}

}  // namespace smt
}  // namespace CVC4
