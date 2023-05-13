/******************************************************************************
 * Top contributors (to current version):
 *   Caleb Donovick, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Remove rewrite rules, apply pre-skolemization to existential quantifiers.
 *
 * Calls the quantifier rewriter, removing rewrite rules and applying
 * pre-skolemization to existential quantifiers
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__QUANTIFIERS_PREPROCESS_H
#define CVC5__PREPROCESSING__PASSES__QUANTIFIERS_PREPROCESS_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class QuantifiersPreprocess : public PreprocessingPass
{
 public:
  QuantifiersPreprocess(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__QUANTIFIERS_PREPROCESS_H */
