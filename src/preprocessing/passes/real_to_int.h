/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The RealToInt preprocessing pass.
 *
 * Converts real operations into integer operations.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__REAL_TO_INT_H
#define CVC5__PREPROCESSING__PASSES__REAL_TO_INT_H

#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class RealToInt : public PreprocessingPass
{
  using NodeMap = context::CDHashMap<Node, Node>;

 public:
  RealToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  Node realToIntInternal(TNode n, NodeMap& cache, std::vector<Node>& var_eq);
  /** Cache for the above method */
  NodeMap d_cache;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__REAL_TO_INT_H */
