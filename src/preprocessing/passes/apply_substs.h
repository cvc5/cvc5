/*********************                                                        */
/*! \file bv_gauss.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief TODO.
 **
 ** TODO
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__APPLY_SUBSTS_H
#define __CVC4__PREPROCESSING__PASSES__APPLY_SUBSTS_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class ApplySubsts : public PreprocessingPass
{
 public:
   ApplySubsts(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * TODO
   * Apply the substitutions in d_topLevelAssertions and the rewriter to each of
   * the assertions in d_assertions, and store the result back in d_assertions.
   * TODO
   */
   PreprocessingPassResult applyInternal(
       AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif

