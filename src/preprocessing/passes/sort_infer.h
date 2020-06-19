/*********************                                                        */
/*! \file sort_infer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sort inference preprocessing pass
 **/

#ifndef CVC4__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_
#define CVC4__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_

#include <map>
#include <string>
#include <vector>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
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
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_ */
