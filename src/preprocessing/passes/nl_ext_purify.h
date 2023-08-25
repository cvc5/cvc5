/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The NlExtPurify preprocessing pass.
 *
 * Purifies non-linear terms by replacing sums under multiplications by fresh
 * variables.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__NL_EXT_PURIFY_H
#define CVC5__PREPROCESSING__PASSES__NL_EXT_PURIFY_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using NodeMap = std::unordered_map<Node, Node>;

class NlExtPurify : public PreprocessingPass
{
 public:
  NlExtPurify(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  Node purifyNlTerms(TNode n,
                     NodeMap& cache,
                     NodeMap& bcache,
                     std::vector<Node>& var_eq,
                     bool beneathMult = false);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__NL_EXT_PURIFY_H */
