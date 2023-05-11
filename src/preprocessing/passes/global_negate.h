/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The global_negate preprocessing pass.
 *
 * Updates a set of assertions to the negation of these assertions.
 * In detail, if assertions is:
 *    F1, ..., Fn
 * then we update this vector to:
 *    forall x1...xm. ~( F1 ^ ... ^ Fn ), true, ..., true
 * where x1...xm are the free variables of F1...Fn.
 * When this is done, d_globalNegation flag is marked, so that the solver
 * checks for unsat instead of sat.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__GLOBAL_NEGATE_H
#define CVC5__PREPROCESSING__PASSES__GLOBAL_NEGATE_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
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
  Node simplify(const std::vector<Node>& assertions, NodeManager* nm);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING_PASSES__GLOBAL_NEGATE_H */
