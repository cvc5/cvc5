/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sort inference preprocessing pass.
 */

#include "preprocessing/passes/sort_infer.h"

#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/theory_engine.h"

using namespace std;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

SortInferencePass::SortInferencePass(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sort-inference")
{
}

PreprocessingPassResult SortInferencePass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  theory::SortInference* si =
      d_preprocContext->getTheoryEngine()->getSortInference();

  if (options().smt.sortInference)
  {
    si->initialize(assertionsToPreprocess->ref());
    std::map<Node, Node> model_replace_f;
    std::map<Node, std::map<TypeNode, Node> > visited;
    for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; i++)
    {
      Node prev = (*assertionsToPreprocess)[i];
      Node next = si->simplify(prev, model_replace_f, visited);
      if (next != prev)
      {
        next = rewrite(next);
        assertionsToPreprocess->replace(i, next);
        Trace("sort-infer-preprocess")
            << "*** Preprocess SortInferencePass " << prev << endl;
        Trace("sort-infer-preprocess")
            << "   ...got " << (*assertionsToPreprocess)[i] << endl;
      }
    }
    std::vector<Node> newAsserts;
    si->getNewAssertions(newAsserts);
    for (const Node& na : newAsserts)
    {
      Node nar = rewrite(na);
      Trace("sort-infer-preprocess")
          << "*** Preprocess SortInferencePass : new constraint " << nar
          << endl;
      assertionsToPreprocess->push_back(nar);
    }
    // could indicate correspondence between the functions
    // for (f1, f2) in model_replace_f, f1's model should be based on f2.
    // See cvc4-wishues/issues/75.

    // only need to compute monotonicity on the resulting formula if we are
    // using this option
    if (options().uf.ufssFairnessMonotone)
    {
      si->computeMonotonicity(assertionsToPreprocess->ref());
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
