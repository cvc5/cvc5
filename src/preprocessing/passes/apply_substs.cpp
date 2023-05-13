/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Gereon Kremer
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

#include "preprocessing/passes/apply_substs.h"

#include "context/cdo.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

ApplySubsts::ApplySubsts(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "apply-substs")
{
}

PreprocessingPassResult ApplySubsts::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  verbose(2) << "applying substitutions..." << std::endl;
  Trace("apply-substs") << "ApplySubsts::processAssertions(): "
                        << "applying substitutions" << std::endl;
  // TODO(#1255): Substitutions in incremental mode should be managed with a
  // proper data structure.

  theory::TrustSubstitutionMap& tlsm =
      d_preprocContext->getTopLevelSubstitutions();
  unsigned size = assertionsToPreprocess->size();
  for (unsigned i = 0; i < size; ++i)
  {
    if (assertionsToPreprocess->isSubstsIndex(i))
    {
      continue;
    }
    Trace("apply-substs") << "applying to " << (*assertionsToPreprocess)[i]
                          << std::endl;
    d_preprocContext->spendResource(Resource::PreprocessStep);
    assertionsToPreprocess->replaceTrusted(
        i,
        tlsm.applyTrusted((*assertionsToPreprocess)[i], d_env.getRewriter()));
    Trace("apply-substs") << "  got " << (*assertionsToPreprocess)[i]
                          << std::endl;
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
