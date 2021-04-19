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
  // objectives for types that doesn't distinguish signed/unsigned
  OBJECTIVE_MINIMIZE,
  OBJECTIVE_MAXIMIZE,
  // no support for minmax and maxmin for now
  // because minmax and maxmin are just syntactic sugar
};

/**
 * The optimization order for multiple objectives
 * Box: treat the objectives as independent objectives
 *    v_x = max(x) w.r.t. phi(x, y)
 *    v_y = max(y) w.r.t. phi(x, y)
 * Lexicographic: optimize the objectives one-by-one
 *    v_x = max(x) w.r.t. phi(x, y)
 *    v_y = max(y) w.r.t. phi(v_x, y)
 * Pareto: optimize multiple goals to a state such that
 *  further optimization of one goal will worsen the other goal(s)
 *    (v_x, v_y) s.t. phi(v_x, v_y) is sat, and
 *      forall (x, y), phi(x, y) -> x <= v_x or y <= v_y
 * **/
enum class ObjectiveOrder
{
  OBJORDER_BOX,
  OBJORDER_LEXICOGRAPHIC,
  OBJORDER_PARETO
};

/**
 * An enum for optimization queries.
 * Represents the result of a checkopt query
 */
enum class OptResult
{
  // objective type is not supported
  OPT_UNSUPPORTED,

  // the original set of assertions has result UNKNOWN
  OPT_UNKNOWN,
  // the original set of assertions has result UNSAT
  OPT_UNSAT,
  // the optimization loop finished and optimal
  OPT_OPTIMAL,
  // the result is unbounded,
  // if maximize, the result is +infinity,
  // if minimize, the result is -infinity
  OPT_UNBOUNDED
};

/**
 * The optimization objective, which contains:
 * - the optimization target node,
 * - whether it's maximize/minimize
 * - and whether it's signed for BitVectors (optional, defaults to false)
 * Use struct here because it's passive objective and it only carries data
 */
struct Objective
{
  /**
   * The node associated to the term that was used to construct the objective.
   **/
  Node d_node;
  /**
   * The type of objective this is,
   * either OBJECTIVE_MAXIMIZE OR OBJECTIVE_MINIMIZE
   **/
  ObjectiveType d_type;
  /**
   * Specify whether to use signed or unsigned comparison
   * for BitVectors (only for BitVectors),
   * this variable is defaulted to false
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
   * @param objOrder the optimization order for multiple objectives
   **/
  OptimizationSolver(SmtEngine* parent,
                     ObjectiveOrder objOrder = ObjectiveOrder::OBJORDER_BOX);
  ~OptimizationSolver() = default;

  /** Runs the optimization loop for the activated objective **/
  OptResult checkOpt();

  /**
   * Push an objective that will be optimized for
   * @param node the Node representing the expression that will be optimized for
   * @param objType specifies whether it's maximize or minimize
   * @param bvSigned specifies whether we should use signed/unsigned
   *   comparison for BitVectors (only effective for BitVectors)
   *   and its default value is false
   **/
  void pushObj(Node node, ObjectiveType objType, bool bvSigned = false);

  /**
   * Pop the most-recently pushed objective
   **/
  void popObj();

  /** Gets the value of the optimized objective after checkopt is called **/
  std::vector<Node> objectiveGetValues();

  /**
   * Specifies how to deal with multigoal optimization
   * @param objOrder the enum specifying the order.
   **/
  void setObjectiveOrder(ObjectiveOrder objOrder);

 private:
  /**
   * Initialize an SMT subsolver for offline optimization purpose
   * @param needsTimeout specifies whether it needs timeout for each single
   *    query
   * @param timeout the timeout value, given in milliseconds (ms)
   * @return a unique_pointer of SMT subsolver
   **/
  std::unique_ptr<SmtEngine> createOptCheckerWithTimeout(
      bool needsTimeout = false, unsigned long timeout = 0);

  /** Optimize multiple goals in Box order, naive implementation **/
  OptResult optimizeBoxNaive();

  /** Optimize multiple goals in Lexicographic order, using iterative
   * implementation **/
  OptResult optimizeLexIterative();

  /** Optimize multiple goals in Pareto order **/
  OptResult optimizeParetoNaive();

  /** The parent SMT engine **/
  SmtEngine* d_parent;

  /** The objectives to optimize for **/
  std::vector<Objective> d_objectives;

  /** A saved value of the objective from the last sat call. **/
  std::vector<Node> d_optValues;

  /** The optimization order for multiple objectives **/
  ObjectiveOrder d_objOrder;

  /** The subchecker specifically for pareto goals,
   * because we need to save the states so that each call would return a
   * different value **/
  std::unique_ptr<SmtEngine> d_optCheckerForPareto;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__OPTIMIZATION_SOLVER_H */
