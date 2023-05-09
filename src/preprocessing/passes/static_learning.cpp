/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Yoni Zohar, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

StaticLearning::StaticLearning(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "static-learning"),
      d_cache(userContext()){};

PreprocessingPassResult StaticLearning::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(Resource::PreprocessStep);

  std::vector<TNode> toProcess;

  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    const Node& n = (*assertionsToPreprocess)[i];

    /* Already processed in this context. */
    if (d_cache.find(n) != d_cache.end())
    {
      continue;
    }

    NodeBuilder learned(kind::AND);
    learned << n;

    /* Process all assertions in nested AND terms. */
    std::vector<TNode> assertions;
    flattenAnd(n, assertions);
    for (TNode a : assertions)
    {
      d_preprocContext->getTheoryEngine()->ppStaticLearn(a, learned);
    }

    if (learned.getNumChildren() == 1)
    {
      learned.clear();
    }
    else
    {
      assertionsToPreprocess->replace(i, rewrite(learned.constructNode()));
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void StaticLearning::flattenAnd(TNode node, std::vector<TNode>& children)
{
  std::vector<TNode> visit = {node};
  do
  {
    TNode cur = visit.back();
    visit.pop_back();

    if (d_cache.find(cur) != d_cache.end())
    {
      continue;
    }
    d_cache.insert(cur);

    if (cur.getKind() == kind::AND)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else
    {
      children.push_back(cur);
    }
  } while (!visit.empty());
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
