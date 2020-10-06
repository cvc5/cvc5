/*********************                                                        */
/*! \file bv_abstraction.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BvAbstraction preprocessing pass
 **
 ** Abstract common structures over small domains to UF. This preprocessing
 ** is particularly useful on QF_BV/mcm benchmarks and can be enabled via
 ** option `--bv-abstraction`.
 ** For more information see 3.4 Refactoring Isomorphic Circuits in [1].
 **
 ** [1] Liana Hadarean, An Efficient and Trustworthy Theory Solver for
 **     Bit-vectors in Satisfiability Modulo Theories
 **     https://cs.nyu.edu/media/publications/hadarean_liana.pdf
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__BV_ABSTRACTION_H
#define CVC4__PREPROCESSING__PASSES__BV_ABSTRACTION_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
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
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__BV_ABSTRACTION_H */
