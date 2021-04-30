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

#include "cvc5_private.h"

#ifndef CVC5__SMT__OPTIMIZATION_SOLVER_H
#define CVC5__SMT__OPTIMIZATION_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "util/result.h"

namespace cvc5 {

class SmtEngine;

namespace smt {

/**
 * The optimization result of an optimization objective
 * containing:
 * - whether it's optimal or not
 * - if so, the optimal value, otherwise the value might be empty node or
 *   something suboptimal
 */
class OptimizationResult
{
 public:
  /**
   * Enum indicating whether the checkOpt result
   * is optimal or not.
   **/
  enum ResultType
  {
    // the type of the target is not supported
    UNSUPPORTED,
    // the original set of assertions has result UNKNOWN
    UNKNOWN,
    // the original set of assertions has result UNSAT
    UNSAT,
    // the optimization loop finished and optimal
    OPTIMAL,
    // the goal is unbounded, so it would be -inf or +inf
    UNBOUNDED,
  };

  /**
   * Constructor
   * @param result the optimization outcome
   * @param value the optimized value
   **/
  OptimizationResult(ResultType type, Node value) : d_type(type), d_value(value)
  {
  }
  OptimizationResult() : d_type(UNSUPPORTED), d_value() {}
  ~OptimizationResult() = default;

  /**
   * Returns an enum indicating whether
   * the result is optimal or not.
   * @return an enum showing whether the result is optimal, unbounded,
   *   unsat, unknown or unsupported.
   **/
  ResultType getType() { return d_type; }
  /**
   * Returns the optimal value.
   * @return Node containing the optimal value,
   *   if getType() is not OPTIMAL, it might return an empty node or a node
   *   containing non-optimal value
   **/
  Node getValue() { return d_value; }

 private:
  ResultType d_type;
  Node d_value;
};

/**
 * The optimization objective, which contains:
 * - the optimization target node,
 * - whether it's maximize/minimize
 * - and whether it's signed for BitVectors
 */
class OptimizationObjective
{
 public:
  /**
   * An enum for optimization queries.
   * Represents whether an objective should be minimized or maximized
   */
  enum ObjectiveType
  {
    MINIMIZE,
    MAXIMIZE,
  };

  /**
   * Constructor
   * @param target the optimization target node
   * @param type speficies whether it's maximize/minimize
   * @param bvSigned specifies whether it's using signed or unsigned comparison
   *    for BitVectors this parameter is only valid when the type of target node
   *    is BitVector
   **/
  OptimizationObjective(Node target, ObjectiveType type, bool bvSigned = false)
      : d_type(type), d_target(target), d_bvSigned(bvSigned)
  {
  }
  ~OptimizationObjective() = default;

  /** A getter for d_type **/
  ObjectiveType getType() { return d_type; }

  /** A getter for d_target **/
  Node getTarget() { return d_target; }

  /** A getter for d_bvSigned **/
  bool bvIsSigned() { return d_bvSigned; }

 private:
  /**
   * The type of objective,
   * it's either MAXIMIZE OR MINIMIZE
   **/
  ObjectiveType d_type;

  /**
   * The node associated to the term that was used to construct the objective.
   **/
  Node d_target;

  /**
   * Specify whether to use signed or unsigned comparison
   * for BitVectors (only for BitVectors), this variable is defaulted to false
   **/
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
  OptimizationSolver(SmtEngine* parent)
      : d_parent(parent), d_objectives(), d_results()
  {
  }
  ~OptimizationSolver() = default;

  /** Runs the optimization loop for the pushed objective **/
  OptimizationResult::ResultType checkOpt();

  /**
   * Pushes an objective
   * @param target the Node representing the expression that will be optimized
   *for
   * @param type specifies whether it's maximize or minimize
   * @param bvSigned specifies whether we should use signed/unsigned
   *   comparison for BitVectors (only effective for BitVectors)
   *   and its default is false
   **/
  void pushObjective(const Node target,
                     const OptimizationObjective::ObjectiveType type,
                     bool bvSigned = false);

  /**
   * Pops the objective that is lastly pushed.
   **/
  void popObjective();

  /**
   * Returns the values of the optimized objective after checkopt is called
   * @return a vector of Optimization Result,
   *   each containing the outcome and the value.
   **/
  std::vector<OptimizationResult> getValues();

 private:
  /** The parent SMT engine **/
  SmtEngine* d_parent;

  /** The objectives to optimize for **/
  std::vector<OptimizationObjective> d_objectives;

  /** The results of the optimizations from the last checkOpt call **/
  std::vector<OptimizationResult> d_results;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__OPTIMIZATION_SOLVER_H */
