/*********************                                                        */
/*! \file bv_gauss.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Gaussian Elimination preprocessing pass.
 **
 ** Simplify a given equation system modulo a (prime) number via Gaussian
 ** Elimination if possible.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__BV_GAUSS_ELIM_H
#define __CVC4__PREPROCESSING__PASSES__BV_GAUSS_ELIM_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class BVGauss : public PreprocessingPass
{
 public:
   BVGauss(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Apply Gaussian Elimination on (possibly multiple) set(s) of equations
   * modulo some (prime) number given as bit-vector equations.
   *
   * Note that these sets of equations do not have to be modulo some prime
   * but can be modulo any arbitrary number. However, GE is guaranteed to
   * succeed modulo a prime number, which is not necessarily the case if a
   * given set of equations is modulo a non-prime number.
   */
   PreprocessingPassResult applyInternal(
       AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
