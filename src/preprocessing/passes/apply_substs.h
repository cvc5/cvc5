/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Apply substitutions preprocessing pass.
 *
 * Apply top level substitutions to assertions, rewrite, and store back into
 * assertions.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__APPLY_SUBSTS_H
#define CVC5__PREPROCESSING__PASSES__APPLY_SUBSTS_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {

class PreprocessingPassContext;

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
}  // namespace cvc5::internal

#endif
