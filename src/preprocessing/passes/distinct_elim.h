/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The distinct_elim preprocessing pass.
 *
 * Eagerly eliminates (blasts) distinct terms into pairwise disequalities,
 * based on a configurable threshold on the number of children.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__DISTINCT_ELIM_H
#define CVC5__PREPROCESSING__PASSES__DISTINCT_ELIM_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class DistinctElim : public PreprocessingPass
{
 public:
  DistinctElim(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   * Traverse n and blast every distinct term whose number of children is at
   * most the threshold. A threshold of 0 means no limit, i.e. all distinct
   * terms are blasted.
   */
  Node convert(TNode n);
  /**
   * The maximum number of children a distinct term may have to be eliminated,
   * or 0 for no limit.
   */
  uint64_t d_threshold;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__DISTINCT_ELIM_H */
