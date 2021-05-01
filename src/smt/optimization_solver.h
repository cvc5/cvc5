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
    // whether the value is optimal is UNKNOWN
    UNKNOWN,
    // the original set of assertions has result UNSAT
    UNSAT,
    // the value is optimal
    OPTIMAL,
    // the goal is unbounded,
    // if objective is maximize, it's +infinity
    // if objective is minimize, it's -infinity
    UNBOUNDED,
  };

  /**
   * Constructor
   * @param type the optimization outcome
   * @param value the optimized value
   **/
  OptimizationResult(ResultType type, TNode value)
      : d_type(type), d_value(value)
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
  /** the indicating whether the result is optimal or something else **/
  ResultType d_type;
  /** if the result is optimal, this is storing the optimal value **/
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
  OptimizationObjective(TNode target, ObjectiveType type, bool bvSigned = false)
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

  /**
   * Run the optimization loop for the pushed objective
   * NOTE: this function currently supports only single objective
   * for multiple pushed objectives it always optimizes the first one.
   * Add support for multi-obj later
   */
  OptimizationResult::ResultType checkOpt();

  /**
   * Push an objective.
   * @param target the Node representing the expression that will be optimized
   *for
   * @param type specifies whether it's maximize or minimize
   * @param bvSigned specifies whether we should use signed/unsigned
   *   comparison for BitVectors (only effective for BitVectors)
   *   and its default is false
   **/
  void pushObjective(TNode target,
                     OptimizationObjective::ObjectiveType type,
                     bool bvSigned = false);

  /**
   * Pop the most recent objective.
   **/
  void popObjective();

  /**
   * Returns the values of the optimized objective after checkOpt is called
   * @return a vector of Optimization Result,
   *   each containing the outcome and the value.
   **/
  std::vector<OptimizationResult> getValues();

 private:
  /**
   * Initialize an SMT subsolver for offline optimization purpose
   * @param parentSMTSolver the parental solver containing the assertions
   * @param needsTimeout specifies whether it needs timeout for each single
   *    query
   * @param timeout the timeout value, given in milliseconds (ms)
   * @return a unique_pointer of SMT subsolver
   **/
  static std::unique_ptr<SmtEngine> createOptCheckerWithTimeout(
      SmtEngine* parentSMTSolver,
      bool needsTimeout = false,
      unsigned long timeout = 0);

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
