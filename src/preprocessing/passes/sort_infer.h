/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
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

#ifndef CVC5__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_
#define CVC5__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/** SortInferencePass
 *
 * This preprocessing pass runs sort inference techniques on the input formula.
 * For details on these techniques, see theory/sort_inference.h.
 */
class SortInferencePass : public PreprocessingPass
{
 public:
  SortInferencePass(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_ */
