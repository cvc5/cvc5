/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Michael Chang, Aina Niemetz
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
  OptimizationResult() : d_type(UNKNOWN), d_value() {}
  ~OptimizationResult() = default;

  /**
   * Returns an enum indicating whether
   * the result is optimal or not.
   * @return an enum showing whether the result is optimal, unbounded,
   *   unsat or unknown.
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
   * An enum specifying how multiple objectives are dealt with.
   * Definition:
   *   phi(x, y): set of assertions with variables x and y
   *
   * Box: treat the objectives as independent objectives
   *   v_x = max(x) s.t. phi(x, y) = sat
   *   v_y = max(y) s.t. phi(x, y) = sat
   *
   * Lexicographic: optimize the objectives one-by-one, in the order they are
   * added:
   *   v_x = max(x) s.t. phi(x, y) = sat 
   *   v_y = max(y) s.t. phi(v_x, y) = sat
   *
   * Pareto: optimize multiple goals to a state such that
   * further optimization of one goal will worsen the other goal(s)
   *   (v_x, v_y) s.t. phi(v_x, v_y) = sat, and
   *     forall (x, y), (phi(x, y) = sat) -> (x <= v_x or y <= v_y)
   **/
  enum ObjectiveCombination
  {
    BOX,
    LEXICOGRAPHIC,
    PARETO,
  };
  /**
   * Constructor
   * @param parent the smt_solver that the user added their assertions to
   **/
  OptimizationSolver(SmtEngine* parent);
  ~OptimizationSolver() = default;

  /**
   * Run the optimization loop for the added objective
   * For multiple objective combination, it defaults to lexicographic,
   * and combination could be set by calling
   *   setObjectiveCombination(BOX/LEXICOGRAPHIC/PARETO)
   */
  OptimizationResult::ResultType checkOpt();

  /**
   * Add an optimization objective.
   * @param target Node representing the expression that will be optimized for
   * @param type specifies whether it's maximize or minimize
   * @param bvSigned specifies whether we should use signed/unsigned
   *   comparison for BitVectors (only effective for BitVectors)
   *   and its default is false
   **/
  void addObjective(TNode target,
                    OptimizationObjective::ObjectiveType type,
                    bool bvSigned = false);

  /**
   * Clear all the added optimization objectives
   **/
  void resetObjectives();

  /**
   * Returns the values of the optimized objective after checkOpt is called
   * @return a vector of Optimization Result,
   *   each containing the outcome and the value.
   **/
  std::vector<OptimizationResult> getValues();

  /**
   * Sets the objective combination
   **/
  void setObjectiveCombination(ObjectiveCombination combination);

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

  /**
   * Optimize multiple goals in Box order
   * @return OPTIMAL if all of the objectives are either OPTIMAL or UNBOUNDED;
   *   UNSAT if at least one objective is UNSAT and no objective is UNKNOWN;
   *   UNKNOWN if any of the objective is UNKNOWN.
   **/
  OptimizationResult::ResultType optimizeBox();

  /**
   * Optimize multiple goals in Lexicographic order,
   * using iterative implementation
   * @return OPTIMAL if all objectives are OPTIMAL and bounded;
   *   UNBOUNDED if one of the objectives is UNBOUNDED
   *     and optimization will stop at that objective;
   *   UNSAT if one of the objectives is UNSAT
   *     and optimization will stop at that objective;
   *   UNKNOWN if one of the objectives is UNKNOWN
   *     and optimization will stop at that objective;
   *   If the optimization is stopped at an objective,
   *     all objectives following that objective will be UNKNOWN.
   **/
  OptimizationResult::ResultType optimizeLexicographicIterative();

  /**
   * Optimize multiple goals in Pareto order
   * Using a variant of linear search called Guided Improvement Algorithm
   * Could be called multiple times to iterate through the Pareto front
   *
   * Definition:
   * Pareto front: Set of all possible Pareto optimal solutions
   *
   * Reference:
   * D. Rayside, H.-C. Estler, and D. Jackson. The Guided Improvement Algorithm.
   *  Technical Report MIT-CSAIL-TR-2009-033, MIT, 2009.
   *
   * @return if it finds a new Pareto optimal result it will return OPTIMAL;
   *   if it exhausts the results in the Pareto front it will return UNSAT;
   *   if the underlying SMT solver returns UNKNOWN, it will return UNKNOWN.
   **/
  OptimizationResult::ResultType optimizeParetoNaiveGIA();

  /** A pointer to the parent SMT engine **/
  SmtEngine* d_parent;

  /** A subsolver for offline optimization **/
  std::unique_ptr<SmtEngine> d_optChecker;

  /** The objectives to optimize for **/
  std::vector<OptimizationObjective> d_objectives;

  /** The results of the optimizations from the last checkOpt call **/
  std::vector<OptimizationResult> d_results;

  /** The current objective combination method **/
  ObjectiveCombination d_objectiveCombination;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__OPTIMIZATION_SOLVER_H */
