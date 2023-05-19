/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The sep-pre-skolem-emp eprocessing pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__SEP_SKOLEM_EMP_H
#define CVC5__PREPROCESSING__PASSES__SEP_SKOLEM_EMP_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class SepSkolemEmp : public PreprocessingPass
{
 public:
  SepSkolemEmp(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__SEP_SKOLEM_EMP_H */
