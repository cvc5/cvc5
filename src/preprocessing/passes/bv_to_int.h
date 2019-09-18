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
 ** Converts bit-vector formulas to integer formulas.
 ** The conversion is implemented using a translation function Tr, roughly
 described as follows:
 **
 ** Tr(x) = fresh_x for every bit-vector variable x, where fresh_x is a fresh
 integer variable.
 ** Tr(c) = the integer value of c, for any bit-vector constant c.
 ** Tr((bvadd s t)) = Tr(s) + Tr(t) mod 2^k, where k is the bit-width of s and
 t.
 ** Similar transformations are done for bvmul, bvsub, bvudiv, bvurem, bvneg,
 bvnot, bvconcat, bvextract

 ** Tr((bvand s t)) depends on the granularity, which is provided by the user
 when enabling this preprocessing pass.
 ** We divide s and t to blocks. 
 ** The size of each block is the granularity, and so there are
 ** bitwidth/granularity blocks (rounded down).
 ** We create an ITE that rebresents an arbitrary block, and then create a sum by mutiplying each block by the appropriate power of two.
 ** More formally:
 ** Let g denote the granularity.
 ** Let k denote the bitwidth of s and t.
 ** Let b denote floor(k/g) if k >= g, or just k otherwise.
 ** Tr((bvand s t)) = Sigma_{i=0}^{b-1}(bvand s[(i+1)*g, i*g] t[(i+1)*g, i*g])*2^(i*g)

 ** More details and examples for this case are described next to
 createBitwiseNode.
 ** Similar transformations are done for bvor, bvxor, bvxnor, bvnand, bvnor.
 **
 ** Tr((bvshl a b)) = ite(Tr(b) >= k, 0, Tr(a)*ITE), where k is the bitwidth of
 a and b, and ITE represents exponentiation up to k, that is:
 ** ITE = ite(Tr(b)=0, 1, ite(Tr(b)=1), 2, ite(Tr(b)=2, 4, ...))
 ** Similar transformations are done for bvlshr.
 **
 ** Tr(a=b) = Tr(a)=Tr(b)
 ** Tr((bvult a b)) = Tr(a) < Tr(b)
 ** Simialr transformations are done for bvule, bvugt, bvuge.
 **
 ** Bit-vector operators that are not listed above are either eliminated using
 the function eliminationPass, or are not supported.
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
   * A generic function that creates a node that represents a bit-wise
   * operation. 
   * x and y are integer operands that correspond to the original
   * bit-vector operands. 
   * bvsize is the bitwidth of the original bit-vector variables. 
   * granularity is specified in the options for this preprocessing pass.
   * f is a pointer to a boolean function that corresponds to the original bit-wise
   * operation.
   *
   * For example: Suppose bvsize is 4, granularity is 1, and f(x,y) = x && y
   * Denote by ITE(a,b) the term: ite(a==0, ite(b==0, 0, 0), ite(b==1, 1, 0)).
   * The result of this function would be:
   * ITE(x[0], y[0])*2^0 + ... + ITE(x[3], y[3])*2^3
   *
   * For another example: Suppose bvsize is 4, granularity is 2, and f(x,y) = x && y. 
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
   * (for example, 2 in binary is 10 and 1 in binary is 01, and so doing
   * "bitwise f" on them gives 00).
   * The result of this function would be:
   * ITE(x[1:0], y[1:0])*2^0 + ITE(x[3:2], y[3:2])*2^2
   */
  Node createBitwiseNode(Node x,
                         Node y,
                         uint64_t bvsize,
                         uint64_t granularity,
                         bool (*f)(bool, bool));

  /** 
   * A helper function for createBitwiseNode
   * x and y are integer nodes that correspond to the original bit-vector nodes.
   * bitwidth represents the bitwidth of the original bit-vector nodes.
   * table represents a function from pairs of integers to integers.
   * The domain of this function consists of pairs of integers between 0 (inclusive) and 2^{bitwidth} (exclusive).
   * The returned node is an ite term that represents this table.
   */
  Node createITEFromTable(
      Node x,
      Node y,
      uint64_t bitwidth,
      std::map<std::pair<uint64_t, uint64_t>, uint64_t> table);

  /**
   * A generic function that creates a logical shift node (either left or
   * right). 
   * a << b gets translated to a * 2^b mod 2^k, where k is the
   * bit-width. 
   * a >> b gets translated to a div 2^b mod 2^k, where k is the
   * bit-width. 
   * The exponentiation operation is translated to an ite for possible
   * values of the exponent, from 0 to k-1. 
   * If the right operand of the shift is greater than k-1,
   * the result is 0.
   *
   */
  Node createShiftNode(vector<Node> children,
                       uint64_t bvsize,
                       bool isLeftShift);

  /**
   * Returns a node that represents the bit-wise negation of n.
   */
  Node createBVNotNode(Node n, uint64_t bvsize);

  /**
   * n is a bit-vector term or formula.
   * The result is an integer term and is computed according to the translation specified above.
   */
  Node bvToInt(Node n);

  /**
   * Whenever we introduce an integer varaible that represents a bit-vector
   * variable, we need to guard the range of the newly introduced variable. For
   * bit-width k, the constraint is 0 <= newVar < 2^k.
   * newVar is the newly introduced integer variable
   * k is the bitwidth of the original bit-vector variable.
   * The result is a node representing the range constraint.
   */
  Node mkRangeConstraint(Node newVar, uint64_t k);

  /**
   * In the translation to integers, it is convenient to assume that certain
   * bit-vector operators do not occur in the original formula (e.g., repeat).
   * This function eliminates all these operators.
   */
  Node eliminationPass(Node n);

  /**
   * Some bit-vector operators (e.g., bvadd, bvand) are binary, but allow more
   * than two arguments as a syntactic sugar. 
   * For example, we can have a node
   * for (bvand x y z), that represents (bvand (x (bvand y z))). 
   * This function
   * makes all such operators strictly binary.
   *
   */
  Node makeBinary(Node n);

  /**
   * input: A non-negative integer k
   * output: A node that represents 2^k
   */
  Node pow2(uint64_t k);

  /**
   * input: A positive integer k
   * output: A node that represent the maximal integer value of a bit-vector of
   * bit-width k.
   * For example, if k is 4, the result is a node representing the
   * constant 15.
   */
  Node maxInt(uint64_t k);

  /**
   * input: A node n, representing an integer term
   * output: A node representing (n mod (2^exponent))
   */
  Node modpow2(Node n, uint64_t exponent);

  /**
   * Add the range assertions collected in d_rangeAssertions (using
   * mkRangeConstraint) to the assertion pipeline. 
   * If there are no range constraints, do nothing. 
   * If there is a single range constraint, add it to
   * the pipeline. 
   * Otherwise, add all of them as a single conjunction
   */
  void addFinalizeRangeAssertions(AssertionPipeline* assertionsToPreprocess);

  /**
   * Caches for the different functions
   */
  NodeMap d_binarizeCache;
  NodeMap d_eliminationCache;
  NodeMap d_bvToIntCache;

  /**
   * Node mangager that is used throughtout the pass
   */
  NodeManager* d_nm;

  /**
   * A set of contraints of the form 0 <= x < 2^k
   * These are added for every new integer variable that we introduce.
   */
  unordered_set<Node, NodeHashFunction> d_rangeAssertions;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H */
