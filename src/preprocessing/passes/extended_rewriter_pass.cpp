/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "smt/env.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ExtRewPre::ExtRewPre(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ext-rew-pre"),
      d_id(options().smt.extRewPrep == options::ExtRewPrepMode::AGG
               ? MethodId::RW_EXT_REWRITE_AGG
               : MethodId::RW_EXT_REWRITE),
      d_proof(options().smt.produceProofs
                  ? new RewriteProofGenerator(d_env, d_id)
                  : nullptr)
{
}

PreprocessingPassResult ExtRewPre::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    const Node& a = (*assertionsToPreprocess)[i];
    Node ar = d_env.rewriteViaMethod(a, d_id);
    assertionsToPreprocess->replace(i, ar, d_proof.get());
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
