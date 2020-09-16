/*********************                                                        */
/*! \file bv_to_int.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BVToInt preprocessing pass
 **
 ** Converts bit-vector formulas to integer formulas.
 ** The conversion is implemented using a translation function Tr,
 ** roughly described as follows:
 **
 ** Tr(x) = fresh_x for every bit-vector variable x, where fresh_x is a fresh
 **         integer variable.
 ** Tr(c) = the integer value of c, for any bit-vector constant c.
 ** Tr((bvadd s t)) = Tr(s) + Tr(t) mod 2^k, where k is the bit width of
 **         s and t.
 ** Similar transformations are done for bvmul, bvsub, bvudiv, bvurem, bvneg,
 **         bvnot, bvconcat, bvextract
 ** Tr((_ zero_extend m) x) = Tr(x)
 ** Tr((_ sign_extend m) x) = ite(msb(x)=0, x, 2^k*(2^m-1) + x))
 ** explanation: if the msb is 0, this is the same as zero_extend,
 ** which does not change the integer value.
 ** If the msb is 1, then the result should correspond to
 ** concat(1...1, x), with m 1's.
 ** m 1's is 2^m-1, and multiplying it by x's width (k) moves it
 ** to the front.
 **
 ** Tr((bvand s t)) depends on the granularity, which is provided by the user
 ** when enabling this preprocessing pass.
 ** We divide s and t to blocks.
 ** The size of each block is the granularity, and so the number of
 ** blocks is:
 ** bit width/granularity (rounded down).
 ** We create an ITE that represents an arbitrary block,
 ** and then create a sum by mutiplying each block by the
 ** appropriate power of two.
 ** More formally:
 ** Let g denote the granularity.
 ** Let k denote the bit width of s and t.
 ** Let b denote floor(k/g) if k >= g, or just k otherwise.
 ** Tr((bvand s t)) =
 ** Sigma_{i=0}^{b-1}(bvand s[(i+1)*g, i*g] t[(i+1)*g, i*g])*2^(i*g)
 **
 ** More details and examples for this case are described next to
 ** the function createBitwiseNode.
 ** Similar transformations are done for bvor, bvxor, bvxnor, bvnand, bvnor.
 **
 ** Tr((bvshl a b)) = ite(Tr(b) >= k, 0, Tr(a)*ITE), where k is the bit width of
 **         a and b, and ITE represents exponentiation up to k, that is:
 ** ITE = ite(Tr(b)=0, 1, ite(Tr(b)=1), 2, ite(Tr(b)=2, 4, ...))
 ** Similar transformations are done for bvlshr.
 **
 ** Tr(a=b) = Tr(a)=Tr(b)
 ** Tr((bvult a b)) = Tr(a) < Tr(b)
 ** Similar transformations are done for bvule, bvugt, and bvuge.
 **
 ** Bit-vector operators that are not listed above are either eliminated using
 ** the function eliminationPass, or are not supported.
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H
#define __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;

class BVToInt : public PreprocessingPass
{
 public:
  BVToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  /**
   * A generic function that creates a node that represents a bitwise
   * operation.
   *
   * For example: Suppose bvsize is 4, granularity is 1, and f(x,y) = x && y.
   * Denote by ITE(a,b) the term: ite(a==0, 0, ite(b==1, 1, 0)).
   * The result of this function would be:
   * ITE(x[0], y[0])*2^0 + ... + ITE(x[3], y[3])*2^3
   *
   * For another example: Suppose bvsize is 4, granularity is 2,
   * and f(x,y) = x && y.
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
   * For example, 2 in binary is 10 and 1 in binary is 01, and so doing
   * "bitwise f" on them gives 00.
   * The result of this function would be:
   * ITE(x[1:0], y[1:0])*2^0 + ITE(x[3:2], y[3:2])*2^2
   *
   *
   * @param x is an integer operand that correspond to the first original
   *        bit-vector operand.
   * @param y is an integer operand that correspond to the second original
   *        bit-vector operand.
   * @param bvsize is the bit width of the original bit-vector variables.
   * @param granularity is specified in the options for this preprocessing
   *        pass.
   * @param f is a pointer to a boolean function that corresponds
   *        to the original bitwise operation.
   * @return A node that represents the operation, as described above.
   */
  Node createBitwiseNode(Node x,
                         Node y,
                         uint64_t bvsize,
                         uint64_t granularity,
                         bool (*f)(bool, bool));

  /**
   * A helper function for createBitwiseNode
   * @param x integer node corresponding to the original first bit-vector
   *        argument
   * @param y integer node corresponding to the original second bit-vector
   *        argument nodes.
   * @param granularity the bitwidth of the original bit-vector nodes.
   * @param table a function from pairs of integers to integers.
   *        The domain of this function consists of pairs of
   *        integers between 0 (inclusive) and 2^{bitwidth} (exclusive).
   * @return An ite term that represents this table.
   */
  Node createITEFromTable(
      Node x,
      Node y,
      uint64_t granularity,
      std::map<std::pair<uint64_t, uint64_t>, uint64_t> table);

  /**
   * A generic function that creates a logical shift node (either left or
   * right). a << b gets translated to a * 2^b mod 2^k, where k is the bit
   * width. a >> b gets translated to a div 2^b mod 2^k, where k is the bit
   * width. The exponentiation operation is translated to an ite for possible
   * values of the exponent, from 0 to k-1.
   * If the right operand of the shift is greater than k-1,
   * the result is 0.
   * @param children the two operands for the shift
   * @param bvsize the original bit widths of the operands
   *                (before translation to integers)
   * @param  isLeftShift true iff the desired operation is a left shift.
   * @return a node representing the shift.
   *
   */
  Node createShiftNode(vector<Node> children,
                       uint64_t bvsize,
                       bool isLeftShift);

  /**
   * Returns a node that represents the bitwise negation of n.
   */
  Node createBVNotNode(Node n, uint64_t bvsize);

  /**
   * The result is an integer term and is computed
   * according to the translation specified above.
   * @param n is a bit-vector term or formula to be translated.
   * @return integer node that corresponds to n.
   */
  Node bvToInt(Node n);

  /**
   * Whenever we introduce an integer variable that represents a bit-vector
   * variable, we need to guard the range of the newly introduced variable.
   * For bit width k, the constraint is 0 <= newVar < 2^k.
   * @param newVar the newly introduced integer variable
   * @param k the bit width of the original bit-vector variable.
   * @return a node representing the range constraint.
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
   * For example, we can have a node for (bvand x y z), 
   * that represents (bvand (x (bvand y z))).
   * This function makes all such operators strictly binary.
   */
  Node makeBinary(Node n);

  /**
   * @param k A non-negative integer
   * @return A node that represents the constant 2^k
   */
  Node pow2(uint64_t k);

  /**
   * @param k A positive integer k
   * @return A node that represent the constant 2^k-1
   * For example, if k is 4, the result is a node representing the
   * constant 15.
   */
  Node maxInt(uint64_t k);

  /**
   * @param n A node representing an integer term
   * @param exponent A non-negative integer
   * @return A node representing (n mod (2^exponent))
   */
  Node modpow2(Node n, uint64_t exponent);

  bool childrenTypesChanged(Node n);

  /**
   * Add the range assertions collected in d_rangeAssertions
   * (using mkRangeConstraint) to the assertion pipeline.
   * If there are no range constraints, do nothing.
   * If there is a single range constraint, add it to the pipeline.
   * Otherwise, add all of them as a single conjunction
   */
  void addFinalizeRangeAssertions(AssertionPipeline* assertionsToPreprocess);

  /**
   * @param quantifiedNode a node whose main operator is forall/exists.
   * @return a node opbtained from quantifiedNode by:
   * 1. Replacing all bound BV variables by new bound integer variables.
   * 2. Add range constraints for the new variables, induced by the original
   * bit-width. These range constraints are added with "AND" in case of exists
   * and with "IMPLIES" in case of forall.
   */
  Node translateQuantifiedFormula(Node quantifiedNode);

  /**
   * Reconstructs a node whose main operator cannot be
   * translated to integers.
   * Reconstruction is done by casting to integers/bit-vectors
   * as needed.
   * For example, if node is (select A x) where A
   * is a bit-vector array, we do not change A to be
   * an integer array, even though x was translated
   * to integers.
   * In this case we cast x to (bv2nat x) during
   * the reconstruction.
   *
   * @param originalNode the node that we are reconstructing
   * @param resultType the desired type for the reconstruction
   * @param translated_children the children of originalNode
   *        after their translation to integers.
   * @return A node with originalNode's operator that has type resultType.
   */
  Node reconstructNode(Node originalNode,
                       TypeNode resultType,
                       const vector<Node>& translated_children);

  /**
   * A useful utility function.
   * if n is an integer and tn is bit-vector,
   * applies the IntToBitVector operator on n.
   * if n is a vit-vector and tn is integer,
   * applies BitVector_TO_NAT operator.
   * Otherwise, keeps n intact.
   */
  Node castToType(Node n, TypeNode tn);

  /**
   * When a UF f is translated to a UF g,
   * we add a define-fun command to the smt-engine
   * to relate between f and g.
   * We do the same when f and g are just variables.
   * This is useful, for example, when asking
   * for a model-value of a term that includes the
   * original UF f.
   * @param bvUF the original function or variable
   * @param intUF the translated function or variable
   */
  void defineBVUFAsIntUF(Node bvUF, Node intUF);

  /**
   * @param bvUF is an uninterpreted function symbol from the original formula
   * @return a fresh uninterpreted function symbol, obtained from bvUF
     by replacing every argument of type BV to an argument of type Integer,
     and the return type becomes integer in case it was BV.
   */
  Node translateFunctionSymbol(Node bvUF);

  /**
   * Performs the actual translation to integers for nodes
   * that have children.
   */
  Node translateWithChildren(Node original,
                             const vector<Node>& translated_children);

  /**
   * Performs the actual translation to integers for nodes
   * that don't have children (variables, constants, uninterpreted function
   * symbols).
   */
  Node translateNoChildren(Node original);

  /**
   * Caches for the different functions
   */
  CDNodeMap d_binarizeCache;
  CDNodeMap d_eliminationCache;
  CDNodeMap d_rebuildCache;
  CDNodeMap d_bvToIntCache;

  /**
   * Node manager that is used throughout the pass
   */
  NodeManager* d_nm;

  /**
   * A set of constraints of the form 0 <= x < 2^k
   * These are added for every new integer variable that we introduce.
   */
  context::CDHashSet<Node, NodeHashFunction> d_rangeAssertions;

  /**
   * Useful constants
   */
  Node d_zero;
  Node d_one;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__BV_TO_INT_H */
