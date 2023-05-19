/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BvIntroPow2 preprocessing pass.
 *
 * Traverses the formula and applies the IsPowerOfTwo rewrite rule. This
 * preprocessing pass is particularly useful on QF_BV/pspace benchmarks and
 * can be enabled via option `--bv-intro-pow2`.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__BV_INTRO_POW2_H
#define CVC5__PREPROCESSING__PASSES__BV_INTRO_POW2_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class BvIntroPow2 : public PreprocessingPass
{
 public:
  BvIntroPow2(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Checks whether PowerOfTwo rewrite applies. */
  bool isPowerOfTwo(TNode node);
  /**
   * Applies PowerOfTwo rewrite.
   *
   * x & (x-1) = 0 => x = 1 << sk
   *
   * where sk is a fresh Skolem.
   *
   * WARNING: this is an **EQUISATISFIABLE** transformation!
   * Only to be called on top level assertions.
   */
  Node rewritePowerOfTwo(TNode node);
  /** Does the traversal of assertions and applies rewritePowerOfTwo. */
  Node pow2Rewrite(Node node, std::unordered_map<Node, Node>& cache);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__BV_INTRO_POW2_H */
