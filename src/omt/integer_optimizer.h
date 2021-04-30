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
 * Optimizer for Integer type.
 */

#ifndef CVC5__OMT__INTEGER_OPTIMIZER_H
#define CVC5__OMT__INTEGER_OPTIMIZER_H

#include "omt/omt_optimizer.h"

namespace cvc5::omt {

/**
 * Optimizer for Integer type
 */
class OMTOptimizerInteger : public OMTOptimizer
{
 public:
  OMTOptimizerInteger() = default;
  virtual ~OMTOptimizerInteger() = default;
  smt::OptimizationResult minimize(SmtEngine* parentSMTSolver,
                                   TNode target) override;
  smt::OptimizationResult maximize(SmtEngine* parentSMTSolver,
                                   TNode target) override;

 private:
  /**
   * Handles the optimization query specified by objType
   * (objType = MINIMIZE / MAXIMIZE)
   **/
  smt::OptimizationResult optimize(
      SmtEngine* parentSMTSolver,
      TNode target,
      smt::OptimizationObjective::ObjectiveType objType);
};

}  // namespace cvc5::omt

#endif /* CVC5__OMT__INTEGER_OPTIMIZER_H */
