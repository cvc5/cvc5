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
    Node createBitwiseNode(vector<Node> children, uint64_t bvsize, uint64_t granularity, uint64_t (*f)(uint64_t, uint64_t));
    Node createITEFromTable(Node x, Node y, uint64_t granularity, std::map<std::pair<uint64_t, uint64_t>, uint64_t> table);
    Node createShiftNode(vector<Node> children, uint64_t bvsize, bool isLeftShift);
    Node createBVNotNode(Node n, uint64_t bvsize);

    Node bvToInt(Node n);
    Node mkRangeConstraint(Node newVar, uint64_t k);
    Node eliminationPass(Node n);
    Node makeBinary(Node n);
    Node pow2(uint64_t k);
    Node maxInt(uint64_t k);
    Node modpow2(Node n, uint64_t exponent);

    NodeMap d_binarizeCache;
    NodeMap d_eliminationCache;
    NodeMap d_bvToIntCache;
    NodeManager* d_nm;
    unordered_set<Node, NodeHashFunction> d_rangeAssertions;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H */
