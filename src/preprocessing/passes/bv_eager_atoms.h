/*********************                                                        */
/*! \file bv_eager_atoms.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Wrap assertions in BITVECTOR_EAGER_ATOM nodes.
 **
 ** This preprocessing pass wraps all assertions in BITVECTOR_EAGER_ATOM nodes
 ** and allows to use eager bit-blasting in the BV solver.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__BV_EAGER_ATOMS_H
#define CVC4__PREPROCESSING__PASSES__BV_EAGER_ATOMS_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
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
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__BV_EAGER_ATOMS_H */
