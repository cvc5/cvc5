/*********************                                                        */
/*! \file int_blaster.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A translation utility from bit-vectors to integers.
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
 ** Tr((bvand s t)) depends on the granularity, which is provided via an option.
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

#ifndef __CVC4__THEORY__BV__INT_BLASTER__H
#define __CVC4__THEORY__BV__INT_BLASTER__H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "context/context.h"
#include "theory/arith/nl/iand_utils.h"
#include "options/smt_options.h"

namespace CVC4 {

using CDNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;

class IntBlaster 
{
 public:
  IntBlaster(SmtEngine* se, options::SolveBVAsIntMode mode);

  /**
   * The result is an integer term and is computed
   * according to the translation specified above.
   * @param n is a bit-vector term or formula to be translated.
   * @return integer node that corresponds to n.
   */
  Node intBlast(Node n);

  Node intBlastWithRanges(Node n);

  // NOTE: this will return all range assertions for the beginning of life of this object.
  Node conjoinRangeAssertions(); 

 protected:
  
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
  Node createShiftNode(std::vector<Node> children,
                       uint64_t bvsize,
                       bool isLeftShift);

  /**
   * Returns a node that represents the bitwise negation of n.
   */
  Node createBVNotNode(Node n, uint64_t bvsize);


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
                       const std::vector<Node>& translated_children);

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
                             const std::vector<Node>& translated_children);

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
  CDNodeMap d_intblastCache;

  /**
   * Node manager that is used throughout the pass
   */
  NodeManager* d_nm;

  /**
   * Range constraints of the form 0 <= x < 2^k
   * These are added for every new integer variable that we introduce.
   */
  context::CDHashSet<Node, NodeHashFunction> d_rangeAssertions;

  /**
   * Useful constants
   */
  Node d_zero;
  Node d_one;
  
  /** helper class for handeling bvand translation */
  theory::arith::nl::IAndUtils d_iandUtils;

  options::SolveBVAsIntMode d_mode;

  SmtEngine* d_se;
};

}  // namespace CVC4

#endif /* __CVC4__THEORY__BV__INT_BLASTER_H */
