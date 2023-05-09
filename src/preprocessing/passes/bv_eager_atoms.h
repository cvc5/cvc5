/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrap assertions in BITVECTOR_EAGER_ATOM nodes.
 *
 * This preprocessing pass wraps all assertions in BITVECTOR_EAGER_ATOM nodes
 * and allows to use eager bit-blasting in the BV solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__BV_EAGER_ATOMS_H
#define CVC5__PREPROCESSING__PASSES__BV_EAGER_ATOMS_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class BvEagerAtoms : public PreprocessingPass
{
 public:
  BvEagerAtoms(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__BV_EAGER_ATOMS_H */
