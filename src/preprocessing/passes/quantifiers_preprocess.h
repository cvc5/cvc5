/*********************                                                        */
/*! \file quantifiers_preprocess.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Remove rewrite rules, apply pre-skolemization to existential
 *quantifiers
 **
 **
 ** Calls the quantifier rewriter, removing rewrite rules and applying
 ** pre-skolemization to existential quantifiers
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__QUANTIFIERS_PREPROCESS_H
#define CVC4__PREPROCESSING__PASSES__QUANTIFIERS_PREPROCESS_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
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
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__QUANTIFIERS_PREPROCESS_H */
