/*********************                                                        */
/*! \file non_clausal_simp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Wu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Non-clausal simplification preprocessing pass.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__SKELETON_PREPROCESSING_H
#define __CVC4__PREPROCESSING__PASSES__SKELETON_PREPROCESSING_H

#include <vector>

#include "prop/cryptominisat.h"

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class SkeletonPreprocessing : public PreprocessingPass
{
 public:
  SkeletonPreprocessing(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
