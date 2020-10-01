/*********************                                                        */
/*! \file global_negate.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief the global_negate preprocessing pass
  * Updates a set of assertions to the negation of
 * these assertions. In detail, if assertions is:
 *    F1, ..., Fn
 * then we update this vector to:
 *    forall x1...xm. ~( F1 ^ ... ^ Fn ), true, ..., true
 * where x1...xm are the free variables of F1...Fn.
 * When this is done, d_globalNegation flag is marked, so that the solver checks
 *for unsat instead of sat.
**/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__GLOBAL_NEGATE_H
#define CVC4__PREPROCESSING__PASSES__GLOBAL_NEGATE_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class GlobalNegate : public PreprocessingPass
{
 public:
  GlobalNegate(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  Node simplify(std::vector<Node>& assertions, NodeManager* nm);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING_PASSES__GLOBAL_NEGATE_H */
