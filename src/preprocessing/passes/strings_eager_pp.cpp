/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The strings eager preprocess utility.
 */

#include "preprocessing/passes/strings_eager_pp.h"

#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_preprocess.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

StringsEagerPp::StringsEagerPp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "strings-eager-pp"){};

PreprocessingPassResult StringsEagerPp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = NodeManager::currentNM();
  theory::strings::SkolemCache skc(nullptr);
  theory::strings::StringsPreprocess pp(d_env, &skc);
  for (size_t i = 0, nasserts = assertionsToPreprocess->size(); i < nasserts;
       ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    std::vector<Node> asserts;
    Node rew = pp.processAssertion(prev, asserts);
    if (!asserts.empty())
    {
      std::vector<Node> conj;
      conj.push_back(rew);
      conj.insert(conj.end(), asserts.begin(), asserts.end());
      rew = nm->mkAnd(conj);
    }
    if (prev != rew)
    {
      assertionsToPreprocess->replace(i, rewrite(rew));
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
