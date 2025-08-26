/******************************************************************************
 * Top contributors (to current version):
 *   Caleb Donovick, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The rewrite preprocessing pass.
 *
 * Calls the rewriter on every assertion.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__REWRITE_H
#define CVC5__PREPROCESSING__PASSES__REWRITE_H

#include "preprocessing/preprocessing_pass.h"
#include "proof/rewrite_proof_generator.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class Rewrite : public PreprocessingPass
{
 public:
  Rewrite(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** The proof generator if proofs are enabled */
  std::unique_ptr<RewriteProofGenerator> d_proof;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__REWRITE_H */
