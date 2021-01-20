/*********************                                                        */
/*! \file optimization_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng
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
//#include <iostream>

using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

OptimizationSolver::OptimizationSolver(SmtEngine* parent) : d_parent(parent)
{
}

OptimizationSolver::~OptimizationSolver() {}

bool OptimizationSolver::checkOpt(Result& r){
    std::vector<Node> axioms = d_parent->getExpandedAssertions();
    std::unique_ptr<SmtEngine> optChecker;
    initializeSubsolver(optChecker);

    optChecker->setOption("incremental", "true");
    optChecker->setOption("produce-models", "true");

    for (const Node& e : axioms){
        optChecker->assertFormula(e);
    }
    
    NodeManager* nm = optChecker->getNodeManager();

    for (int i = 0; i < d_activatedObjectives.size(); i++)
    {
      optChecker->push();
      Objective o = d_activatedObjectives[i];
      // CVC4::Kind k = o.d_node.getKind();

      r = optChecker->checkSat();

      Result loop_r = r;

      while (loop_r.isSat())
      {
        Node value = optChecker->getValue(o.d_node);
        o.d_savedValue = value;
        Node increment;
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

void OptimizationSolver::activateObj(const Node& obj, const int& type, const int& result){
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