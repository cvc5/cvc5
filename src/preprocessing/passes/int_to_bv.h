/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The IntToBV preprocessing pass.
 *
 * Converts integer operations into bitvector operations. The width of the
 * bitvectors is controlled through the `--solve-int-as-bv` command line
 * option.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__INT_TO_BV_H
#define CVC5__PREPROCESSING__PASSES__INT_TO_BV_H

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using NodeMap = std::unordered_map<Node, Node>;

class IntToBV : public PreprocessingPass
{
 public:
  IntToBV(PreprocessingPassContext* preprocContext);
  Node intToBV(TNode n, NodeMap& cache);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__INT_TO_BV_H */
