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

#include "context/cdhashmap_forward.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "util/result.h"

namespace cvc5 {

class SmtEngine;

namespace smt {

/**
 * The optimization result of an optimization objective
 * containing:
 * - the optimization result: SAT/UNSAT/UNKNOWN
 * - the optimal value if SAT and bounded
 *     (optimal value reached and it's not infinity),
 *   or an empty node if SAT and unbounded
 *     (optimal value is +inf for maximum or -inf for minimum),
 *   otherwise the value might be empty node
 *   or something suboptimal
 * - whether the objective is unbounded
 */
class OptimizationResult
{
 public:
  /**
   * Constructor
   * @param type the optimization outcome
   * @param value the optimized value
   * @param unbounded whether the objective is unbounded
   **/
  OptimizationResult(Result result, TNode value, bool unbounded = false)
      : d_result(result), d_value(value), d_unbounded(unbounded)
  {
  }
  OptimizationResult()
      : d_result(Result::Sat::SAT_UNKNOWN,
                 Result::UnknownExplanation::NO_STATUS),
        d_value(),
        d_unbounded(false)
  {
  }
  ~OptimizationResult() = default;

  /**
   * Returns an enum indicating whether
   * the result is SAT or not.
   * @return whether the result is SAT, UNSAT or SAT_UNKNOWN
   **/
  Result getResult() const { return d_result; }

  /**
   * Returns the optimal value.
   * @return Node containing the optimal value,
   *   if result is unbounded, this will be an empty node,
   *   if getResult() is UNSAT, it will return an empty node,
   *   if getResult() is SAT_UNKNOWN, it will return something suboptimal
   *   or an empty node, depending on how the solver runs.
   **/
  Node getValue() const { return d_value; }

  /**
   * Checks whether the objective is unbouned
   * @return whether the objective is unbounded
   *   if the objective is unbounded (this function returns true), 
   *   then the optimal value is:
   *   +inf, if it's maximize;
   *   -inf, if it's minimize
   **/
  bool isUnbounded() const { return d_unbounded; }

 private:
  /** indicating whether the result is SAT, UNSAT or UNKNOWN **/
  Result d_result;
  /** if the result is bounded, this is storing the value **/
  Node d_value;
  /** whether the objective is unbounded
   * If this is true, then:
   * if objective is maximize, it's +infinity;
   * if objective is minimize, it's -infinity
   **/
  bool d_unbounded;
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
  ObjectiveType getType() const { return d_type; }

  /** A getter for d_target **/
  Node getTarget() const { return d_target; }

  /** A getter for d_bvSigned **/
  bool bvIsSigned() const { return d_bvSigned; }

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
   * possible combinations: BOX, LEXICOGRAPHIC, PARETO
   * @param combination BOX / LEXICOGRAPHIC / PARETO
   */
  Result checkOpt(ObjectiveCombination combination = LEXICOGRAPHIC);

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

  /**
   * Optimize multiple goals in Box order
   * @return SAT if all of the objectives are optimal or unbounded;
   *   UNSAT if at least one objective is UNSAT and no objective is SAT_UNKNOWN;
   *   SAT_UNKNOWN if any of the objective is SAT_UNKNOWN.
   **/
  Result optimizeBox();

  /**
   * Optimize multiple goals in Lexicographic order,
   * using iterative implementation
   * @return SAT if the objectives are optimal,
   *     if one of the objectives is unbounded,
   *     the optimization will stop at that objective;
   *   UNSAT if any of the objectives is UNSAT
   *     and optimization will stop at that objective;
   *   SAT_UNKNOWN if any of the objectives is UNKNOWN
   *     and optimization will stop at that objective;
   *   If the optimization is stopped at an objective,
   *     all objectives following that objective will be SAT_UNKNOWN.
   **/
  Result optimizeLexicographicIterative();

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
   * @return if it finds a new Pareto optimal result it will return SAT;
   *   if it exhausts the results in the Pareto front it will return UNSAT;
   *   if the underlying SMT solver returns SAT_UNKNOWN,
   *   it will return SAT_UNKNOWN.
   **/
  Result optimizeParetoNaiveGIA();

  /** A pointer to the parent SMT engine **/
  SmtEngine* d_parent;

  /** A subsolver for offline optimization **/
  std::unique_ptr<SmtEngine> d_optChecker;

  /** The objectives to optimize for **/
  context::CDList<OptimizationObjective> d_objectives;

  /** The results of the optimizations from the last checkOpt call **/
  std::vector<OptimizationResult> d_results;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__OPTIMIZATION_SOLVER_H */
