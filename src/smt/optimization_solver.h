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

#include "cvc4_private.h"

#ifndef CVC5__SMT__OPTIMIZATION_SOLVER_H
#define CVC5__SMT__OPTIMIZATION_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/assertions.h"
#include "util/result.h"

namespace cvc5 {

class SmtEngine;

namespace smt {

/**
 * An enum for optimization queries.
 *
 * Represents whether an objective should be minimized or maximized
 */
enum class ObjectiveType
{
  OBJECTIVE_MINIMIZE,
  OBJECTIVE_MAXIMIZE,
  OBJECTIVE_UNDEFINED
};

/**
 * An enum for optimization queries.
 *
 * Represents the result of a checkopt query
 * (unimplemented) OPT_OPTIMAL: if value was found
 */
enum class OptResult
{
  // the original set of assertions has result UNKNOWN
  OPT_UNKNOWN,
  // the original set of assertions has result UNSAT
  OPT_UNSAT,
  // the optimization loop finished and optimal
  OPT_OPTIMAL,

  // the goal is unbounded, so it would be -inf or +inf
  OPT_UNBOUNDED,

  // The last value is here as a preparation for future work
  // in which pproximate optimizations will be supported.

  // if the solver halted early and value is only approximate
  OPT_SAT_APPROX
};

/**
 * The optimization objective, which contains:
 * - the optimization target node,
 * - whether it's maximize/minimize
 * - and whether it's signed for BitVectors
 */
class Objective
{
 public:
  /**
   * Constructor
   * @param n the optimization target node
   * @param type speficies whether it's maximize/minimize
   * @param bvSigned specifies whether it's using signed or unsigned comparison
   *    for BitVectors this parameter is only valid when the type of target node
   *    is BitVector
   **/
  Objective(Node n, ObjectiveType type, bool bvSigned = false);
  ~Objective(){};

  /** A getter for d_type **/
  ObjectiveType getType();
  /** A getter for d_node **/
  Node getNode();
  /** A getter for d_bvSigned **/
  bool getSigned();

 private:
  /** The type of objective this is, either OBJECTIVE_MAXIMIZE OR
   * OBJECTIVE_MINIMIZE  **/
  ObjectiveType d_type;
  /** The node associated to the term that was used to construct the objective.
   * **/
  Node d_node;

  /** Specify whether to use signed or unsigned comparison
   * for BitVectors (only for BitVectors), this variable is defaulted to false
   * **/
  bool d_bvSigned;
};

/**
 * A solver for optimization queries.
 *
 * This class is responsible for responding to optmization queries. It
 * spawns a subsolver SmtEngine that captures the parent assertions and
 * implements a linear optimization loop. Supports activateObjective,
 * checkOpt, and objectiveGetValue in that order.
 */
class OptimizationSolver
{
 public:
  /**
   * Constructor
   * @param parent the smt_solver that the user added their assertions to
   **/
  OptimizationSolver(SmtEngine* parent);
  ~OptimizationSolver();

  /** Runs the optimization loop for the activated objective **/
  OptResult checkOpt();
  /**
   * Activates an objective: will be optimized for
   * @param obj the Node representing the expression that will be optimized for
   * @param type specifies whether it's maximize or minimize
   * @param bvSigned specifies whether we should use signed/unsigned
   *   comparison for BitVectors (only effective for BitVectors)
   *   and its default is false
   **/
  void activateObj(const Node& obj,
                   const ObjectiveType type,
                   bool bvSigned = false);
  /** Gets the value of the optimized objective after checkopt is called **/
  Node objectiveGetValue();

 private:
  /** The parent SMT engine **/
  SmtEngine* d_parent;
  /** The objectives to optimize for **/
  Objective d_activatedObjective;
  /** A saved value of the objective from the last sat call. **/
  Node d_savedValue;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__OPTIMIZATION_SOLVER_H */
