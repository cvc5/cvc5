/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ExtRewPre preprocessing pass.
 *
 * Applies the extended rewriter to assertions.
 */

#include "preprocessing/passes/extended_rewriter_pass.h"

#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ExtRewPre::ExtRewPre(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ext-rew-pre"){};

PreprocessingPassResult ExtRewPre::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(
        i,
        extendedRewrite(
            (*assertionsToPreprocess)[i],
            options().smt.extRewPrep == options::ExtRewPrepMode::AGG));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
