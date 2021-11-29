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
#include "omt/opt_util.h"
#include "util/result.h"

namespace cvc5 {

class Env;
class SolverEngine;

namespace smt {

/**
 * A solver for optimization queries.
 *
 * This class is responsible for responding to optmization queries. It
 * spawns a subsolver SolverEngine that captures the parent assertions and
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
  OptimizationSolver(SolverEngine* parent);
  ~OptimizationSolver() = default;

  /**
   * Run the optimization loop for the added objective
   * For multiple objective combination, it defaults to lexicographic,
   * possible combinations: BOX, LEXICOGRAPHIC, PARETO
   * @param combination BOX / LEXICOGRAPHIC / PARETO
   */
  Result checkOpt(omt::ObjectiveCombination combination =
                      omt::ObjectiveCombination::LEXICOGRAPHIC);

  /**
   * Add an optimization objective.
   * @param target Node representing the expression that will be optimized for
   * @param type specifies whether it's maximize or minimize,
   *   or unsigned maximize / minimize for BV
   **/
  void addObjective(TNode target, omt::OptType type);

  /**
   * Clear all objectives
   */
  void clearObjectives();

  /** Whether the node is an optimization target */
  bool isOptTarget(TNode n);

  /** 
   * Retrieve the optimal value, 
   * if target is not an objective or the optimization failed, it will return null 
   */
  Node getOptValue(TNode target);

 private:
  /**
   * Initialize an SMT subsolver for offline optimization purpose
   * @param env the environment, which determines options and logic for the
   * subsolver
   * @param parentSMTSolver the parental solver containing the assertions
   * @param needsTimeout specifies whether it needs timeout for each single
   *    query
   * @param timeout the timeout value, given in milliseconds (ms)
   * @return a unique_pointer of SMT subsolver
   **/
  static std::unique_ptr<SolverEngine> createOptCheckerWithTimeout(
      SolverEngine* parentSMTSolver,
      bool needsTimeout = false,
      unsigned long timeout = 0);

  /**
   * Optimize multiple goals in Box order
   * @return SAT if all of the objectives are optimal (could be infinite);
   *   UNSAT if at least one objective is UNSAT and no objective is SAT_UNKNOWN;
   *   SAT_UNKNOWN if any of the objective is SAT_UNKNOWN.
   **/
  Result optimizeBox();

  /**
   * Optimize multiple goals in Lexicographic order,
   * using iterative implementation
   * @return SAT if the objectives are optimal,
   *     if one of the objectives is unbounded (result is infinite),
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
  SolverEngine* d_parent;

  /** A subsolver for offline optimization **/
  std::unique_ptr<SolverEngine> d_optChecker;

  /** The objectives to optimize for **/
  std::vector<omt::Objective> d_objectives;

  /** The lookup table for finding if a target is an objective */
  std::unordered_map<Node, size_t> d_targetLookup;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__OPTIMIZATION_SOLVER_H */
