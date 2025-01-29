/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ExtRewPre preprocessing pass.
 *
 * Applies the extended rewriter to assertions.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__EXTENDED_REWRITER_PASS_H
#define CVC5__PREPROCESSING__PASSES__EXTENDED_REWRITER_PASS_H

#include "preprocessing/preprocessing_pass.h"
#include "proof/rewrite_proof_generator.h"

namespace cvc5::internal {
class CDProof;
namespace preprocessing {
namespace passes {

class ExtRewPre : public PreprocessingPass
{
 public:
  ExtRewPre(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /** The method id, determining the kind of rewrite */
  MethodId d_id;
  /** The proof generator if proofs are enabled */
  std::unique_ptr<RewriteProofGenerator> d_proof;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__EXTENDED_REWRITER_PASS_H */
