/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5::omt {

/**
 * The base class for optimizers of individual CVC type
 */
class OMTOptimizer
{
 public:
  virtual ~OMTOptimizer() = default;
  /**
   * Given a target node, retrieve an optimizer specific for the node's type
   * the second field isSigned specifies whether we should use signed comparison
   * for BitVectors and it's only valid when the type is BitVector
   *
   * @param objective the target objective, which contains the target node
   *   for the expression to be optimized and
   *   whether the expression is signed if the type of node is BitVector
   * @return a unique_pointer pointing to a derived class of OMTOptimizer
   *   and this is the optimizer for targetNode
   **/
  static std::unique_ptr<OMTOptimizer> getOptimizerForObjective(
      smt::Objective objective);

  /**
   * Returns the [less than] and [less than equal to] operators for parameter
   *target
   * @param objective the target objective to optimize
   * @return a pair of <less than operator, less than or equal to operator>
   **/
  static std::pair<Kind, Kind> getLTLEOperator(smt::Objective objective);

  /**
   * Minimize the target node with constraints encoded in optChecker
   *
   * This function is REQUIRED to restore the assertions in optChecker!
   *
   * @param optChecker an SMT solver encoding the assertions as the
   *   constraints
   * @param target the target expression to optimize
   * @return pair<OptResult, Node>: the result of optimization and the optimized
   *   value, if OptResult is OPT_UNKNOWN, value returned could be empty node or
   *   something suboptimal.
   **/
  virtual std::pair<smt::OptResult, Node> minimize(SmtEngine* optChecker,
                                                   Node target) = 0;
  /**
   * Maximize the target node with constraints encoded in optChecker
   *
   * This function is REQUIRED to restore the assertions in optChecker!
   *
   * @param optChecker an SMT solver encoding the assertions as the
   *   constraints
   * @param target the target expression to optimize
   * @return pair<OptResult, Node>: the result of optimization and the optimized
   *   value, if OptResult is OPT_UNKNOWN, value returned could be empty node or
   *   something suboptimal.
   **/
  virtual std::pair<smt::OptResult, Node> maximize(SmtEngine* optChecker,
                                                   Node target) = 0;
};

}  // namespace cvc5::omt

#endif /* CVC5__OMT__OMT_OPTIMIZER_H */
