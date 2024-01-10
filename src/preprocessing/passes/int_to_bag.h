/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Yehonatan Calinsky
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The int-to-bag preprocessing pass.
 */

#ifndef __CVC5__PREPROCESSING__PASSES__INT_TO_BAG_H
#define __CVC5__PREPROCESSING__PASSES__INT_TO_BAG_H


#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/int_blaster.h"

namespace cvc5::internal {
    namespace preprocessing {
        namespace passes {
            class IntToBag : public PreprocessingPass {
            public:
                IntToBag(PreprocessingPassContext *preprocContext);

            protected:
                PreprocessingPassResult applyInternal(
                        AssertionPipeline *assertionsToPreprocess) override;
            };

        }  // namespace passes
    }  // namespace preprocessing
}  // namespace cvc5::internal

#endif //__CVC5__PREPROCESSING__PASSES__INT_TO_BAG_H
