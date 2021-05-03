/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The static learning preprocessing pass.
 */

#include "preprocessing/passes/static_learning.h"

#include <string>

#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

StaticLearning::StaticLearning(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "static-learning"){};

PreprocessingPassResult StaticLearning::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(Resource::PreprocessStep);

  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    NodeBuilder learned(kind::AND);
    learned << (*assertionsToPreprocess)[i];
    d_preprocContext->getTheoryEngine()->ppStaticLearn(
        (*assertionsToPreprocess)[i], learned);
    if (learned.getNumChildren() == 1)
    {
      learned.clear();
    }
    else
    {
      assertionsToPreprocess->replace(
          i, theory::Rewriter::rewrite(learned.constructNode()));
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
