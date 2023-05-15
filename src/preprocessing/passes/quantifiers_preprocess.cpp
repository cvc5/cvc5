/******************************************************************************
 * Top contributors (to current version):
 *   Caleb Donovick, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Remove rewrite rules, apply pre-skolemization to existential quantifiers.
 *
 * Calls the quantifier rewriter, removing rewrite rules and applying
 * pre-skolemization to existential quantifiers
 */

#include "preprocessing/passes/quantifiers_preprocess.h"

#include "base/output.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/quantifiers/quantifiers_preprocess.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;

QuantifiersPreprocess::QuantifiersPreprocess(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "quantifiers-preprocess"){};

PreprocessingPassResult QuantifiersPreprocess::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  size_t size = assertionsToPreprocess->size();
  quantifiers::QuantifiersPreprocess qp(d_env);
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    TrustNode trn = qp.preprocess(prev);
    if (!trn.isNull())
    {
      Node next = trn.getNode();
      assertionsToPreprocess->replace(i, rewrite(next));
      Trace("quantifiers-preprocess") << "*** Pre-skolemize " << prev << endl;
      Trace("quantifiers-preprocess")
          << "   ...got " << (*assertionsToPreprocess)[i] << endl;
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
