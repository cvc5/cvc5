/*********************                                                        */
/*! \file bv_intro_pow2.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BvIntroPow2 preprocessing pass
 **
 ** Traverses the formula and applies the IsPowerOfTwo rewrite rule. This
 ** preprocessing pass is particularly useful on QF_BV/pspace benchmarks and
 ** can be enabled via option `--bv-intro-pow2`.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__BV_INTRO_POW2_H
#define CVC4__PREPROCESSING__PASSES__BV_INTRO_POW2_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class BvIntroPow2 : public PreprocessingPass
{
 public:
  BvIntroPow2(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__BV_INTRO_POW2_H */
