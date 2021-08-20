/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The TheoryRewriteEq preprocessing pass.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__THEORY_REWRITE_EQ_H
#define CVC5__PREPROCESSING__PASSES__THEORY_REWRITE_EQ_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "proof/trust_node.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

/**
 * Implements the preprocessing pass for called ppRewrite on all equalities
 * in the input. This is required to be a preprocessing pass since it is not
 * recommended that ppRewrite is called on equalities generated in lemmas (e.g.
 * it may interfere with equality splitting in theory combination).
 */
class TheoryRewriteEq : public PreprocessingPass
{
 public:
  TheoryRewriteEq(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   * Rewrite the assertion based on rewriting equalities based on theory
   * specific rewriting.
   * An example is removing arithmetic equalities via:
   *   (= x y) ---> (and (>= x y) (<= x y))
   * Returns the trust node corresponding to the rewrite.
   */
  TrustNode rewriteAssertion(TNode assertion);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5

#endif /* CVC5__PREPROCESSING__PASSES__THEORY_REWRITE_EQ_H */
