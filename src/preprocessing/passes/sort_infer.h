/*********************                                                        */
/*! \file pass.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SortInferencePass
 **/

#ifndef __CVC4__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_
#define __CVC4__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/sort_inference.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** SortInferencePass
 *
 * This preprocessing pass runs sort inference techniques on the input formula
 */
class SortInferencePass : public PreprocessingPass
{
 public:
  SortInferencePass(PreprocessingPassContext* preprocContext,
                    SortInference* si);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** pointer to the sort inference module */
  SortInference* d_si;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__SORT_INFERENCE_PASS_H_ */
