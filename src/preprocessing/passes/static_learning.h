/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Mathias Preiner, Aina Niemetz
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

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__STATIC_LEARNING_H
#define CVC5__PREPROCESSING__PASSES__STATIC_LEARNING_H

#include "context/cdhashset.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class StaticLearning : public PreprocessingPass
{
 public:
  StaticLearning(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Collect children of flattened AND term. */
  void flattenAnd(TNode node, std::vector<TNode>& children);

  /** CD-cache for visiting nodes used by `flattenAnd`. */
  context::CDHashSet<Node> d_cache;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__STATIC_LEARNING_H */
