/*********************                                                        */
/*! \file bv_to_int.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar and Ahmed Irfan
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BVToInt preprocessing pass
 **
 ** Converts bitvector operations into integer operations. 
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

    /**
     * A generic function that creates a node that represents a bit-wise operation.
     * x and y are integer operands that correspond to the original bit-vector operands
     * bvsize is the bitwidth of x and y
     * granularity is specified in the options for this preprocessing pass (TODO specify!)
     * f is a pointer to a boolean function that corresponds to the original bit-wise operation.
     *
     * For example: Suppose bvsize is 4, granularity is 1, and f(x,y) = x && y
     * Denote by ITE(a,b) the term: ite(a==0, ite(b==0, 0, 0), ite(b==1, 1, 0)).
     * The result of this function would be:
     * ITE(x[0], y[0])*2^0 + ... + ITE(x[3], y[3])*2^3
     *
     * For another example: Suppose bvsize is 4, granularity is 2, and f(x,y) = x && y
     * Denote by ITE(a,b) the term that corresponds to the following table:
     * a | b |  ITE(a,b)
     * ----------------
     * 0 | 0 | 0
     * 0 | 1 | 0
     * 0 | 2 | 0
     * 0 | 3 | 0
     * 1 | 0 | 0
     * 1 | 1 | 1
     * 1 | 2 | 0
     * 1 | 3 | 1
     * 2 | 0 | 0
     * 2 | 1 | 0
     * 2 | 2 | 2
     * 2 | 3 | 2
     * 3 | 0 | 0
     * 3 | 1 | 1
     * 3 | 2 | 2
     * 3 | 3 | 3
     *
     * (for example, 2 in binary is 10 and 1 in binary is 01, and so doing "bitwise f" on them fives 00)
     * The result of this function would be:
     * ITE(x[1:0], y[1:0])*2^0 + ITE(x[3:2], y[3:2])*2^1
     */
    Node createBitwiseNode(Node x, Node y, uint64_t bvsize, uint64_t granularity, bool (*f)(bool, bool));

    //A helper function for createBitwiseNode
    Node createITEFromTable(Node x, Node y, uint64_t granularity, std::map<std::pair<uint64_t, uint64_t>, uint64_t> table);

    /**
     * A generic function that creates a logical shift node (either left or right).
     * a << b gets translated to a * 2^b mod 2^k, where k is the bit-width. 
     * a >> b gets translated to a div 2^b mod 2^k, where k is the bit-width
     * The exponentiation operation is translated to an ite for possible values of the exponent, from 0 to k-1.
     *
     */
    Node createShiftNode(vector<Node> children, uint64_t bvsize, bool isLeftShift);
    Node createBVNotNode(Node n, uint64_t bvsize);

    Node bvToInt(Node n);
    Node mkRangeConstraint(Node newVar, uint64_t k);
    Node eliminationPass(Node n);
    Node makeBinary(Node n);
    Node pow2(uint64_t k);
    Node maxInt(uint64_t k);
    Node modpow2(Node n, uint64_t exponent);
    void addFinalizeRangeAssertions(AssertionPipeline* assertionsToPreprocess);

    NodeMap d_binarizeCache;
    NodeMap d_eliminationCache;
    NodeMap d_bvToIntCache;
    NodeManager* d_nm;
    /**
     * If there are no range constraints, do nothing.
     * If there is a single range constraint, add it to the assrtions.
     * Otherwise, add all of them as a single conjunction
     */
    unordered_set<Node, NodeHashFunction> d_rangeAssertions;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H */
