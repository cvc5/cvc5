/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BvAbstraction preprocessing pass.
 *
 * Abstract common structures over small domains to UF. This preprocessing
 * is particularly useful on QF_BV/mcm benchmarks and can be enabled via
 * option `--bv-abstraction`.
 * For more information see 3.4 Refactoring Isomorphic Circuits in [1].
 *
 * [1] Liana Hadarean, An Efficient and Trustworthy Theory Solver for
 *     Bit-vectors in Satisfiability Modulo Theories
 *     https://cs.nyu.edu/media/publications/hadarean_liana.pdf
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__BV_ABSTRACTION_H
#define CVC5__PREPROCESSING__PASSES__BV_ABSTRACTION_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

class BvAbstraction : public PreprocessingPass
{
 public:
  BvAbstraction(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PASSES__BV_ABSTRACTION_H */
