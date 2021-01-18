/*********************                                                        */
/*! \file strings_eager_pp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The strings eager preprocess utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__STRINGS_EAGER_PP_H
#define CVC4__PREPROCESSING__PASSES__STRINGS_EAGER_PP_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/**
 * Eliminate all extended string functions in the input problem using
 * reductions to bounded string quantifiers.
 */
class StringsEagerPp : public PreprocessingPass
{
 public:
  StringsEagerPp(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__STRINGS_EAGER_PP_H */
