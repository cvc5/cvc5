/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A translation utility from bit-vectors to integers.
 */

#include "cvc5_private.h"

#ifndef __CVC5__THEORY__BV__INT_BLASTER__H
#define __CVC5__THEORY__BV__INT_BLASTER__H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "options/smt_options.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/iand_utils.h"

namespace cvc5::internal {

/*
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
** bvor, bvxor, bvxnor, bvnand, bvnor -- are eliminated and so bvand is the
*only bit-wise operator that is directly handled.
**
** Tr((bvshl a b)) = ite(Tr(b) >= k, 0, Tr(a)*ITE), where k is the bit width of
**         a and b, and ITE represents exponentiation up to k, that is:
** ITE = ite(Tr(b)=0, 1, ite(Tr(b)=1), 2, ite(Tr(b)=2, 4, ...))
** Similar transformations are done for bvlshr.
**
** Tr(a=b) = Tr(a)=Tr(b)
** Tr((bvult a b)) = Tr(a) < Tr(b)
** Similar transformations are done for bvule, bvugt, and bvuge.
** Tr((bvslt a b)) = Tr(uts(a)) < Tr(uts(b)),
** where uts is a function that transforms unsigned
** to signed representations. See more details
** in the documentation of the function uts.
** Similar transformations are done for the remaining comparators.
**
** Bit-vector operators that are not listed above are either
** eliminated using the BV rewriter,
** or go through the following default
** translation, that also works for non-bit-vector operators
** with result type BV:
** Tr((op t1 ... tn)) = (bv2nat (op (cast t1) ... (cast tn)))
** where (cast x) is ((_ nat2bv k) x) or just x,
** depending on the type of the corresponding argument of
** op.
**
**/
class IntBlaster : protected EnvObj
{
  using CDNodeMap = context::CDHashMap<Node, Node>;

 public:
  /**
   * Constructor.
   * @param context user context
   * @param mode bv-to-int translation mode
   * @param granularity bv-to-int translation granularity
   * translated to integer variables, or are directly casted using `bv2nat`
   * operator. not purely bit-vector nodes.
   */
  IntBlaster(Env& env,
             options::SolveBVAsIntMode mode,
             uint64_t granluarity = 1);

  ~IntBlaster();

  /**
   * The result is an integer term and is computed
   * according to the translation specified above.
   * @param n is a bit-vector term or formula to be translated.
   * @param lemmas additional lemmas that are needed for the translation
   * to be sound. These are range constraints on introduced variables.
   * @param skolems a map in which the following information will be stored
   * during the run of intBlast: for each BV variable n, skolems[n] is its new
   * definition: ((_ nat2bv k) nn), where k is the bit-width of n, and nn is the
   * integer variable that corresponds to n.
   * For each UF f from BV to BV, skolems[f] is lambda x : BV[k] . ((_ nat2bv i)
   * ff((bv2nat x))), where k is the bit-width of the domain of f, i is the
   * bit-width of its range, and ff is a Int->Int function that corresponds to
   * f. For functions with other signatures this is similar
   * @return integer node that corresponds to n
   */
  Node intBlast(Node n,
                std::vector<Node>& lemmas,
                std::map<Node, Node>& skolems);

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
                       uint32_t bvsize,
                       bool isLeftShift);

  /** Adds the constraint 0 <= node < 2^size to lemmas */
  void addRangeConstraint(Node node, uint32_t size, std::vector<Node>& lemmas);

  /** Adds a constraint that encodes bitwise and */
  void addBitwiseConstraint(Node bitwiseConstraint, std::vector<Node>& lemmas);

  /** Returns a node that represents the bitwise negation of n. */
  Node createBVNotNode(Node n, uint32_t bvsize);

  /** Returns a node that represents the arithmetic negation of n. */
  Node createBVNegNode(Node n, uint32_t bvsize);

  /** Returns a node that represents the bitwise and of x and y, based on the
   * provided option. */
  Node createBVAndNode(Node x,
                       Node y,
                       uint32_t bvsize,
                       std::vector<Node>& lemmas);

  /** Returns a node that represents the bitwise or of x and y, by translation
   * to sum and bitwise and. */
  Node createBVOrNode(Node x,
                      Node y,
                      uint32_t bvsize,
                      std::vector<Node>& lemmas);

  /** Returns a node that represents the sum of x and y. */
  Node createBVAddNode(Node x, Node y, uint32_t bvsize);

  /** Returns a node that represents the difference of x and y. */
  Node createBVSubNode(Node x, Node y, uint32_t bvsize);

  /** Returns a node that represents the signed extension of x by amount. */
  Node createSignExtendNode(Node x, uint32_t bvsize, uint32_t amount);

  /**
   * Whenever we introduce an integer variable that represents a bit-vector
   * variable, we need to guard the range of the newly introduced variable.
   * For bit width k, the constraint is 0 <= newVar < 2^k.
   * @param newVar the newly introduced integer variable
   * @param k the bit width of the original bit-vector variable.
   * @return a node representing the range constraint.
   */
  Node mkRangeConstraint(Node newVar, uint32_t k);

  /**
   * Some bit-vector operators (e.g., bvadd, bvand) are binary, but allow more
   * than two arguments as a syntactic sugar.
   * For example, we can have a node for (bvand x y z),
   * that represents (bvand (x (bvand y z))).
   * This function locally binarizes these operators.
   * In the above example, this means that x,y,z
   * are not handled recursively, but will require a separate
   * call to the function.
   *
   */
  Node makeBinary(Node n);

  /**
   * @param k A non-negative integer
   * @return A node that represents the constant 2^k
   */
  Node pow2(uint32_t k);

  /**
   * @param k A positive integer k
   * @return A node that represent the constant 2^k-1
   * For example, if k is 4, the result is a node representing the
   * constant 15.
   */
  Node maxInt(uint32_t k);

  /**
   * @param n A node representing an integer term
   * @param exponent A non-negative integer
   * @return A node representing (n mod (2^exponent))
   */
  Node modpow2(Node n, uint32_t exponent);

  /**
   * Returns true iff the type of at least
   * one child of n was changed by the translation.
   */
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
   * if n is a bit-vector and tn is integer,
   * applies BitVector_TO_NAT operator.
   * Otherwise, keeps n intact.
   */
  Node castToType(Node n, TypeNode tn);

  /**
   * When a UF f is translated to a UF g,
   * we compute a definition
   * to relate between f and g.
   * We do the same when f and g are just variables.
   * This is useful, for example, when asking
   * for a model-value of a term that includes the
   * original UF f.
   *
   * For example: if bvUF is a BV variable x and
   * intUF is an integer variable xx,
   * the return value is ((_ nat2bv k) xx),
   * where k is the width of k.
   *
   * For another example: if bvUF is a BV to BV function
   * f and intUF is an integer to integer function ff,
   * the return value is:
   * lambda x : BV[k]. ((_ nat2bv k) (ff (bv2nat x))),
   * where k is the bit-width of the co-domain of f.
   *
   * @param bvUF the original function or variable
   * @param intUF the translated function or variable
   */
  Node defineBVUFAsIntUF(Node bvUF, Node intUF);

  /**
   * @param bvUF is an uninterpreted function symbol from the original formula
   * @return a fresh uninterpreted function symbol, obtained from bvUF
     by replacing every argument of type BV to an argument of type Integer,
     and the return type becomes integer in case it was BV.
   */
  Node translateFunctionSymbol(Node bvUF, std::map<Node, Node>& skolems);

  /**
   * returns an integer m such that the unsigned
   * binary representation of n is the same as the
   * signed binary representation of m.
   */
  Node uts(Node n, uint32_t bvsize);

  /**
   * Performs the actual translation to integers for nodes
   * that have children.
   */
  Node translateWithChildren(Node original,
                             const std::vector<Node>& translated_children,
                             std::vector<Node>& lemmas);

  /**
   * Performs the actual translation to integers for nodes
   * that don't have children (variables, constants, uninterpreted function
   * symbols).
   */
  Node translateNoChildren(Node original,
                           std::vector<Node>& lemmas,
                           std::map<Node, Node>& skolems);

  /** Caches for the different functions */
  CDNodeMap d_binarizeCache;
  CDNodeMap d_intblastCache;

  /** Node manager that is used throughout the pass */
  NodeManager* d_nm;

  /**
   * Range constraints of the form 0 <= x < 2^k
   * These are added for every new integer variable that we introduce.
   */
  context::CDHashSet<Node> d_rangeAssertions;

  /**
   * A set of "bitwise" equalities over integers for BITVECTOR_AND
   *   used in for options::SolveBVAsIntMode::BITWISE
   */
  context::CDHashSet<Node> d_bitwiseAssertions;

  /** Useful constants */
  Node d_zero;
  Node d_one;

  /** helper class for handeling bvand translation */
  theory::arith::nl::IAndUtils d_iandUtils;

  /** the mode for translation to integers */
  options::SolveBVAsIntMode d_mode;

  /** an SolverEngine for context */
  context::Context* d_context;

  /** the granularity to use in the translation */
  uint32_t d_granularity;
};

}  // namespace cvc5::internal

#endif /* __CVC5__THEORY__BV__INT_BLASTER_H */
