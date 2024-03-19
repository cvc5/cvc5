/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * replace disjunctive bit constraints with polynomial bit constraints
 *
 * example: x = 0 OR x = 1 becomes x * x = x
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__FF_DISJUNCTIVE_BIT_H
#define CVC5__PREPROCESSING__PASSES__FF_DISJUNCTIVE_BIT_H

// external includes

// std includes

// internal includes
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class FfDisjunctiveBit : public PreprocessingPass
{
 public:
  FfDisjunctiveBit(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__FF_DISJUNCTIVE_BIT_H */
