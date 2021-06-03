/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Remove ITEs from the assertions.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ITE_REMOVAL_H
#define CVC5__PREPROCESSING__PASSES__ITE_REMOVAL_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

class IteRemoval : public PreprocessingPass
{
 public:
  IteRemoval(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(AssertionPipeline* assertions) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif  // CVC5__PREPROCESSING__PASSES__ITE_REMOVAL_H
