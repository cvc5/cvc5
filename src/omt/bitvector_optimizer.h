/*********************                                                        */
/*! \file bitvector_optimizer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yancheng Ou
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Optimizer for BitVector type
 **/

#ifndef CVC4__OMT__BITVECTOR_OPTIMIZER_H
#define CVC4__OMT__BITVECTOR_OPTIMIZER_H

#include "omt_optimizer.h"

namespace CVC4::smt {

/**
 * Optimizer for BitVector type
 */
class OMTOptimizerBitVector : public OMTOptimizer
{
 public:
  OMTOptimizerBitVector(bool isSigned);
  virtual ~OMTOptimizerBitVector() = default;
  virtual std::pair<OptResult, Node> minimize(SmtEngine* parentSMTSolver,
                                              Node target) override;
  virtual std::pair<OptResult, Node> maximize(SmtEngine* parentSMTSolver,
                                              Node target) override;

 private:
  /**
   * Computes the BitVector version of (a + b) / 2 without overflow,
   * rounding towards -infinity: -1.5 --> -2 and 1.5 --> 1
   * same as the rounding scheme for int32_t
   **/
  BitVector computeAverage(const BitVector& a,
                           const BitVector& b,
                           bool isSigned);
  /** Creates an SMT subsolver for offline optimization purpose **/
  std::unique_ptr<SmtEngine> createOptChecker(SmtEngine* parentSMTSolver);
  /** Is the BitVector doing signed comparison? **/
  bool d_isSigned;
};

}  // namespace CVC4::smt

#endif /* CVC4__OMT__BITVECTOR_OPTIMIZER_H */
