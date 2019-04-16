/*********************                                                        */
/*! \file bv_to_int.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BVToInt preprocessing pass
 **
 ** Converts bitvector operations into integer operations. 
 ** options: all-ite, some-ite, no-ite -- level of ite (instead of expanding with Sigma).
 ** 
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H
#define __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {


using NodeMap = std::unordered_map<Node, Node, NodeHashFunction>;

class BVToInt : public PreprocessingPass
{
 public:
  BVToInt(PreprocessingPassContext* preprocContext);

 protected:
    PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

    Node bvToInt(Node n);
    Node mkRangeConstraint(Node newVar, size_t k);
    Node eliminationPass(Node n);
    Node makeBinary(Node n);
    Node pow2(size_t k);
    Node pow2(Node n);

    NodeMap d_binarizeCache;
    NodeMap d_eliminationCache;
    NodeMap d_bvToIntCache;
    NodeManager* d_nm;
    vector<Node> d_rangeAssertions;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H */
