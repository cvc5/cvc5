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

  // std::cerr << "b" << std::endl;
  std::unique_ptr<OMTOptimizer> optimizer = 
    OMTOptimizer::getOptimizerForNode(d_activatedObjective.getNode(), d_activatedObjective.getSigned());

  Assert(optimizer != nullptr);

  std::pair<OptResult, CVC4::Node> optResult;
  // std::cerr << "a" << std::endl;
  if (d_activatedObjective.getType() == OBJECTIVE_MAXIMIZE) {
    optResult = optimizer->maximize(this->d_parent, this->d_activatedObjective.getNode());
  } else if (d_activatedObjective.getType() == OBJECTIVE_MINIMIZE) {
    optResult = optimizer->minimize(this->d_parent, this->d_activatedObjective.getNode());
  }

  this->d_savedValue = optResult.second;
  return optResult.first;
}

void OptimizationSolver::activateObj(const Node& obj,
                                     const int& type,
                                     bool bv_is_signed_compare)
{
  d_activatedObjective =
      Objective(obj, (ObjectiveType)type, bv_is_signed_compare);
}

Node OptimizationSolver::objectiveGetValue()
{
  Assert(!d_savedValue.isNull());
  return d_savedValue;
}

Kind OptimizationSolver::getLessThanOperatorForObjective()
{
  // the datatype of the objective
  // currently we support Integer/Real and BitVector
  // gets the objective datatype with type checking
  TypeNode objective_type = this->d_activatedObjective.getNode().getType(true);

  if (objective_type.isInteger() || objective_type.isReal())
  {
    // Integer and Real both share the same LT operator
    return kind::LT;
  }
  else if (objective_type.isBitVector())
  {
    // is it signed comparison?
    if (this->d_activatedObjective.getSigned())
    {
      // signed comparison for BitVectors
      return kind::BITVECTOR_SLT;
    }
    else
    {
      // unsigned comparison for BitVectors
      return kind::BITVECTOR_ULT;
    }
  }  // FloatingPoints?
  else
  {
    // the current objective datatype is not-yet supported
    // or doesn't support comparison (no total order)
    return kind::NULL_EXPR;
  }
}

Objective::Objective(Node obj, ObjectiveType type, bool bv_is_signed_compare)
    : d_type(type), d_node(obj), d_signed(bv_is_signed_compare)
{
}

ObjectiveType Objective::getType() { return d_type; }

Node Objective::getNode() { return d_node; }

bool Objective::getSigned() { return d_signed; }

}  // namespace smt
}  // namespace CVC4
