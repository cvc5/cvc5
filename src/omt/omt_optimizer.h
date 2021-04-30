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
   * @param targetNode the target node for the expression to be optimized
   * @param isSigned speficies whether to use signed comparison for BitVectors
   *   and it's only valid when the type of targetNode is BitVector
   * @return a unique_pointer pointing to a derived class of OMTOptimizer
   *   and this is the optimizer for targetNode
   **/
  static std::unique_ptr<OMTOptimizer> getOptimizerForNode(
      TNode targetNode, bool isSigned = false);

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
   * Minimize the target node with constraints encoded in parentSMTSolver
   *
   * @param parentSMTSolver an SMT solver encoding the assertions as the
   *   constraints
   * @param target the target expression to optimize
   * @return smt::OptimizationResult the result of optimization, containing
   *   whether it's optimal and the optimized value.
   **/
  virtual smt::OptimizationResult minimize(SmtEngine* parentSMTSolver,
                                           TNode target) = 0;
  /**
   * Maximize the target node with constraints encoded in parentSMTSolver
   *
   * @param parentSMTSolver an SMT solver encoding the assertions as the
   *   constraints
   * @param target the target expression to optimize
   * @return smt::OptimizationResult the result of optimization, containing
   *   whether it's optimal and the optimized value.
   **/
  virtual smt::OptimizationResult maximize(SmtEngine* parentSMTSolver,
                                           TNode target) = 0;
};

}  // namespace cvc5::omt

#endif /* CVC5__OMT__OMT_OPTIMIZER_H */
