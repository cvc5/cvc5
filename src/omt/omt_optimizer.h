/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The base class for optimizers of individual cvc5 type.
 */

#ifndef CVC5__OMT__OMT_OPTIMIZER_H
#define CVC5__OMT__OMT_OPTIMIZER_H

#include "smt/optimization_solver.h"

namespace cvc5::internal::omt {

/**
 * The base class for optimizers of individual CVC type
 */
class OMTOptimizer
{
 public:
  virtual ~OMTOptimizer() = default;

  /**
   * Returns whether node supports optimization
   * Currently supported: BitVectors, Integers (preliminary).
   * @param node the target node to check for optimizability
   * @return whether node supports optimization
   **/
  static bool nodeSupportsOptimization(TNode node);

  /**
   * Given an optimization objective,
   * retrieve an optimizer specific for the optimization target
   * @param objective the an OptimizationObjective object containing
   *   the optimization target, whether it's maximized or minimized
   *   and whether it's signed for BV (only applies when the target type is BV)
   * @return a unique_pointer pointing to a derived class of OMTOptimizer
   *   and this is the optimizer for targetNode
   **/
  static std::unique_ptr<OMTOptimizer> getOptimizerForObjective(
      const smt::OptimizationObjective& objective);

  /**
   * Given the lhs and rhs expressions, with an optimization objective,
   * makes an incremental expression stating that
   *   lhs `better than` rhs
   * under the context specified by objective
   * for minimize, it would be lhs < rhs
   * for maximize, it would be lhs > rhs
   *
   * Note: the types of lhs and rhs nodes must match or be convertable
   *   to the type of the optimization target!
   *
   * @param nm the NodeManager to manage the made expression
   * @param lhs the left hand side of the expression
   * @param rhs the right hand side of the expression
   * @param objective the optimization objective
   *   stating whether it's maximize / minimize etc.
   * @return an expression stating lhs `better than` rhs,
   **/
  static Node mkStrongIncrementalExpression(
      NodeManager* nm,
      TNode lhs,
      TNode rhs,
      const smt::OptimizationObjective& objective);

  /**
   * Given the lhs and rhs expressions, with an optimization objective,
   * makes an incremental expression stating that
   *   lhs `better than or equal to` rhs
   * under the context specified by objective
   * for minimize, it would be lhs <= rhs
   * for maximize, it would be lhs >= rhs
   *
   * Note: the types of lhs and rhs nodes must match or be convertable
   *   to the type of the optimization target!
   *
   * @param nm the NodeManager to manage the made expression
   * @param lhs the left hand side of the expression
   * @param rhs the right hand side of the expression
   * @param objective the optimization objective
   *   stating whether it's maximize / minimize etc.
   * @return an expression stating lhs `better than or equal to` rhs,
   **/
  static Node mkWeakIncrementalExpression(
      NodeManager* nm,
      TNode lhs,
      TNode rhs,
      const smt::OptimizationObjective& objective);

  /**
   * Minimize the target node with constraints encoded in optChecker
   *
   * @param optChecker an SMT solver encoding the assertions as the
   *   constraints
   * @param target the target expression to optimize
   * @return smt::OptimizationResult the result of optimization, containing
   *   whether it's optimal and the optimized value.
   **/
  virtual smt::OptimizationResult minimize(SolverEngine* optChecker,
                                           TNode target) = 0;
  /**
   * Maximize the target node with constraints encoded in optChecker
   *
   * @param optChecker an SMT solver encoding the assertions as the
   *   constraints
   * @param target the target expression to optimize
   * @return smt::OptimizationResult the result of optimization, containing
   *   whether it's optimal and the optimized value.
   **/
  virtual smt::OptimizationResult maximize(SolverEngine* optChecker,
                                           TNode target) = 0;
};

}  // namespace cvc5::internal::omt

#endif /* CVC5__OMT__OMT_OPTIMIZER_H */
