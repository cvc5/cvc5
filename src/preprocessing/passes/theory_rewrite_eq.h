/*********************                                                        */
/*! \file theory_rewrite_eq.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The TheoryRewriteEq preprocessing pass
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__THEORY_REWRITE_EQ_H
#define CVC4__PREPROCESSING__PASSES__THEORY_REWRITE_EQ_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/trust_node.h"

namespace CVC4 {
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
  theory::TrustNode rewriteAssertion(TNode assertion);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__THEORY_REWRITE_EQ_H */
