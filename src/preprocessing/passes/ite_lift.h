/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocessing pass that lifts if-then-else terms out of theory predicates.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ITE_LIFT_H
#define CVC5__PREPROCESSING__PASSES__ITE_LIFT_H

#include <memory>
#include <unordered_map>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "proof/conv_proof_generator.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Lifts if-then-else terms out of equalities and arithmetic comparisons whose
 * other argument is a variable or constant, e.g.
 *   (= x (ite c t (ite d s r))) ---> (ite c (= x t) (ite d (= x s) (= x r)))
 * This avoids introducing fresh variables for the if-then-else terms during
 * term formula removal. It is applied before simplification, since otherwise
 * equalities such as the one above may be used as substitutions, which moves
 * the if-then-else terms into contexts where they cannot be lifted.
 */
class IteLift : public PreprocessingPass
{
 public:
  IteLift(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Lift if-then-else terms out of all predicates in n */
  Node convert(TNode n);
  /**
   * Lift if-then-else terms out of n if it is an equality or arithmetic
   * comparison whose other argument is a variable or constant. Returns n
   * otherwise. If proofs are enabled, this records a rewrite step for each
   * single lifting step.
   */
  Node liftAtom(const Node& n);
  /**
   * Whether the if-then-else tree of t is small enough for lifting, i.e. the
   * number of distinct nodes reachable from t via branches of if-then-else
   * terms is bounded. Lifting larger trees, e.g. ones with shared subterms in
   * large if-then-else DAGs, may introduce too many atoms.
   */
  bool isSmallIteTree(TNode t) const;
  /** Cache for convert */
  std::unordered_map<Node, Node> d_cache;
  /**
   * Cache for liftAtom. This is required since if-then-else terms may share
   * subterms, in which case lifting without a cache takes time exponential in
   * the nesting depth.
   */
  std::unordered_map<Node, Node> d_liftCache;
  /**
   * The term conversion proof generator, if proofs are enabled. It is not
   * user-context dependent, since the caches above are not either.
   */
  std::unique_ptr<TConvProofGenerator> d_tpg;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__ITE_LIFT_H */
