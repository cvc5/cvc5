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
 * Optimizer for BitVector type.
 */

#ifndef CVC5__OMT__BITVECTOR_OPTIMIZER_H
#define CVC5__OMT__BITVECTOR_OPTIMIZER_H

#include "omt/omt_optimizer.h"

namespace cvc5::internal::omt {

/**
 * Optimizer for BitVector type
 */
class OMTOptimizerBitVector : public OMTOptimizer
{
 public:
  OMTOptimizerBitVector(bool isSigned);
  virtual ~OMTOptimizerBitVector() = default;
  smt::OptimizationResult minimize(SolverEngine* optChecker,
                                   TNode target) override;
  smt::OptimizationResult maximize(SolverEngine* optChecker,
                                   TNode target) override;

 private:
  /**
   * Computes the BitVector version of (a + b) / 2 without overflow,
   * rounding towards -infinity: -1.5 --> -2 and 1.5 --> 1
   * same as the rounding scheme for int32_t
   **/
  BitVector computeAverage(const BitVector& a,
                           const BitVector& b,
                           bool isSigned);
  /** Is the BitVector doing signed comparison? **/
  bool d_isSigned;
};

}  // namespace cvc5::internal::omt

#endif /* CVC5__OMT__BITVECTOR_OPTIMIZER_H */
