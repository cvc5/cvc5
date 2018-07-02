/*********************                                                        */
/*! \file apply_substs.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Apply substitutions preprocessing pass.
 **
 ** Apply top level substitutions to assertions, rewrite, and store back into
 ** assertions.
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
   * Apply assertionsToPreprocess->getTopLevelSubstitutions() to the
   * assertions, in assertionsToPreprocess, rewrite, and store back into
   * given assertion pipeline.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
