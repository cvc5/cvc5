/*********************                                                        */
/*! \file real_to_int.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The RealToInt preprocessing pass
 **
 ** Converts real operations into integer operations
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__REAL_TO_INT_H
#define CVC4__PREPROCESSING__PASSES__REAL_TO_INT_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using NodeMap = std::unordered_map<Node, Node, NodeHashFunction>;

class RealToInt : public PreprocessingPass
{
 public:
  RealToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  Node realToIntInternal(TNode n, NodeMap& cache, std::vector<Node>& var_eq);
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__REAL_TO_INT_H */
