/*********************                                                        */
/*! \file static_learning.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The static learning preprocessing pass
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__STATIC_LEARNING_H
#define CVC4__PREPROCESSING__PASSES__STATIC_LEARNING_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class StaticLearning : public PreprocessingPass
{
 public:
  StaticLearning(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__STATIC_LEARNING_H */
