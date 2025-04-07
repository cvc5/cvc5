/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic entailment computation for string terms.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__ARITH_ENTAIL_H
#define CVC5__THEORY__STRINGS__ARITH_ENTAIL_H

#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

class TConvProofGenerator;

namespace theory {

class Rewriter;

namespace strings {

/**
 * Techniques for computing arithmetic entailment for string terms. This
 * is an implementation of the techniques from Reynolds et al, "High Level
 * Abstractions for Simplifying Extended String Constraints in SMT", CAV 2019.
 */
class ArithEntail
{
 public:
  /**
   * @param r The rewriter, used for rewriting arithmetic terms. If none
   * is provided, we rely on the ArithPolyNorm utility.
   * @param recApprox Whether to use recursive arithmetic approxiations in this
   * class.
   */
  ArithEntail(NodeManager* nm, Rewriter* r, bool recApprox = false);
  /**
   * Returns the rewritten form of a term, which must be an integer term.
   * This method invokes the rewriter, if one is provided, and uses the
   * ArithPolyNorm utility (arith/arith_poly_norm.h) otherwise.
   */
  Node rewriteArith(Node a);
  /**
   * Normalize the integer relation n to a GEQ, if possible.
   * For example, (> t s) becomes (>= t (+ s 1)). Returns null if n is
   * not an arithmetic relation {>,>=,<,<=} over integers.
   * @param n The relation to normalize.
   * @return a GEQ term equivalent to n, if one exists.
   */
  Node normalizeGeq(const Node& n) const;
  /**
   * Do basic length intro rewrites in all subterms of n.
   * For example, calling this method on
   *   (= (str.len (str.++ x "A")) 4)
   * returns:
   *   (= (+ (str.len x) 1) 4)
   * @param n The term to rewrite.
   * @param pg If provided, we add small step rewrites that were performed to n
   * such that pg can provide a proof of (= n n'), where n' is the term returned
   * by this class.
   * @return The result of rewriting length terms in n.
   */
  Node rewriteLengthIntro(const Node& n,
                          TConvProofGenerator* pg = nullptr) const;
  /** check arithmetic entailment equal
   * Returns true if it is always the case that a = b.
   */
  bool checkEq(Node a, Node b);
  /** check arithmetic entailment
   * @param a The first term.
   * @param b The second term
   * @param strict Whether we are testing strict inequality.
   * @param isSimple If true, then we do not use approximations for recursive
   * calls when computing approximations.
   * @return true if it is always the case a >= b, or a > b if strict is true.
   */
  bool check(Node a, Node b, bool strict = false, bool isSimple = false);
  /** check arithmetic entailment
   * Returns true if it is always the case that a >= 0.
   * @param a The term.
   * @param strict Whether we are testing strict inequality.
   * @param isSimple If true, then we do not use approximations for recursive
   * calls when computing approximations.
   * @return true if it is always the case a >= 0, or a > 0 if strict is true.
   */
  bool check(Node a, bool strict = false, bool isSimple = false);

  /**
   * Checks whether assumption |= a >= 0 (if strict is false) or
   * assumption |= a > 0 (if strict is true), where assumption is an equality
   * assumption. The assumption must be in rewritten form.
   *
   * Example:
   *
   * checkWithEqAssumption(x + (str.len y) = 0, -x, false) = true
   *
   * Because: x = -(str.len y), so -x >= 0 --> (str.len y) >= 0 --> true
   */
  bool checkWithEqAssumption(Node assumption, Node a, bool strict = false);

  /**
   * Checks whether assumption |= a >= b (if strict is false) or
   * assumption |= a > b (if strict is true). The function returns true if it
   * can be shown that the entailment holds and false otherwise. Assumption
   * must be in rewritten form. Assumption may be an equality or an inequality.
   *
   * Example:
   *
   * checkWithAssumption(x + (str.len y) = 0, 0, x, false) = true
   *
   * Because: x = -(str.len y), so 0 >= x --> 0 >= -(str.len y) --> true
   *
   * Since this method rewrites on rewriting and may introduce new variables
   * (slack variables for inequalities), it should *not* be called from the
   * main rewriter of strings, or non-termination can occur.
   */
  bool checkWithAssumption(Node assumption,
                           Node a,
                           Node b,
                           bool strict = false);

  /**
   * Checks whether assumptions |= a >= b (if strict is false) or
   * assumptions |= a > b (if strict is true). The function returns true if it
   * can be shown that the entailment holds and false otherwise. Assumptions
   * must be in rewritten form. Assumptions may be an equalities or an
   * inequalities.
   *
   * Example:
   *
   * checkWithAssumptions([x + (str.len y) = 0], 0, x, false) = true
   *
   * Because: x = -(str.len y), so 0 >= x --> 0 >= -(str.len y) --> true
   *
   * Since this method rewrites on rewriting and may introduce new variables
   * (slack variables for inequalities), it should *not* be called from the
   * main rewriter of strings, or non-termination can occur.
   */
  bool checkWithAssumptions(std::vector<Node> assumptions,
                            Node a,
                            Node b,
                            bool strict = false);

  /** get arithmetic lower bound
   * If this function returns a non-null Node ret,
   * then ret is a rational constant and
   * we know that n >= ret always if isLower is true,
   * or n <= ret if isLower is false.
   *
   * Notice the following invariant.
   * If getConstantArithBound(a, true) = ret where ret is non-null, then for
   * strict = { true, false } :
   *   ret >= strict ? 1 : 0
   *     if and only if
   *   check( a, strict ) = true.
   */
  Node getConstantBound(TNode a, bool isLower = true);

  /**
   * Get constant bound on the length of s, if it can be determined. This
   * method will always worst case return 0 as a lower bound.
   */
  Node getConstantBoundLength(TNode s, bool isLower = true) const;
  /**
   * Given an inequality y1 + ... + yn >= x, removes operands yi s.t. the
   * original inequality still holds. Returns true if the original inequality
   * holds and false otherwise. The list of ys is modified to contain a subset
   * of the original ys.
   *
   * Example:
   *
   * inferZerosInSumGeq( (str.len x), [ (str.len x), (str.len y), 1 ], [] )
   * --> returns true with ys = [ (str.len x) ] and zeroYs = [ (str.len y), 1 ]
   *     (can be used to rewrite the inequality to false)
   *
   * inferZerosInSumGeq( (str.len x), [ (str.len y) ], [] )
   * --> returns false because it is not possible to show
   *     str.len(y) >= str.len(x)
   */
  bool inferZerosInSumGeq(Node x,
                          std::vector<Node>& ys,
                          std::vector<Node>& zeroYs);

  /**
   * Find approximation of a such that it can be shown to be greater than
   * zero.
   *
   * Returns a non-null node if it is always the case that a >= 0. We expect
   * that a is in rewritten form.
   *
   * This function uses "approximation" techniques that under-approximate
   * the value of a for the purposes of showing the entailment holds. For
   * example, given:
   *   len( x ) - len( substr( y, 0, len( x ) ) )
   * Since we know that len( substr( y, 0, len( x ) ) ) <= len( x ), the above
   * term can be under-approximated as len( x ) - len( x ) = 0, which is >= 0,
   * and thus the entailment len( x ) - len( substr( y, 0, len( x ) ) ) >= 0
   * holds.
   *
   * @param a The node to find approximations for.
   * @param isSimple If true, then we are only making recursive calls to check
   * without approximations to determine the set of possible approximations.
   * @return The approximated form of a, call it aa, such that a >= aa is
   * entailed by the theory, and aa can be shown to be greater than zero (using
   * checkSimple).
   */
  Node findApprox(Node a, bool isSimple = false);

  /**
   * Check entail arithmetic simple.
   * Returns true if we can show a >= 0 always. This uses the fact that
   * string length is non-negative but otherwise uses only basic properties
   * of arithmetic.
   * This method assumes that a is in rewritten form.
   */
  static bool checkSimple(Node a);

  /**
   * Rewrite the arithmetic predicate n based on string arithmetic entailment.
   *
   * We require that n is either an equality or GEQ between integers.
   *
   * This returns the term true or false if it is the case that n can be
   * rewritten to that constant. This method returns null otherwise.
   *
   * If this returns a non-null node, then exp is updated to the term that
   * we proved was always greater than or equal to zero. For example,
   * given input:
   * (= (str.len x) (- 5)), we return the false term and set exp to
   * (- (- (str.len x) (- 5)) 1), since this term is always non-negative.
   *
   * @param n The arithmetic predicate (EQUAL or GEQ) to rewrite.
   * @param exp The explanation term, if we return non-null.
   * @return the Boolean constant that n can be rewritten to, or null if none
   * exists.
   */
  Node rewritePredViaEntailment(const Node& n,
                                Node& exp,
                                bool isSimple = false);
  /**
   * Same as above, without an explanation.
   */
  Node rewritePredViaEntailment(const Node& n, bool isSimple = false);

 private:
  /**
   * Helper for findApprox, called when the approximation for a is not in the
   * cache.
   */
  Node findApproxInternal(Node a, bool isSimple);
  /** Get arithmetic approximations
   *
   * This gets the (set of) arithmetic approximations for term a and stores
   * them in approx. If isOverApprox is true, these are over-approximations
   * for the value of a, otherwise, they are underapproximations. For example,
   * an over-approximation for len( substr( y, n, m ) ) is m; an
   * under-approximation for indexof( x, y, n ) is -1.
   *
   * Notice that this function is not generally recursive (although it may make
   * a small bounded of recursive calls). Instead, it returns the shape
   * of the approximations for a. For example, an under-approximation
   * for the term len( replace( substr( x, 0, n ), y, z ) ) returned by this
   * function might be len( substr( x, 0, n ) ) - len( y ), where we don't
   * consider (recursively) the approximations for len( substr( x, 0, n ) ).
   */
  void getArithApproximations(Node a,
                              std::vector<Node>& approx,
                              bool isOverApprox = false,
                              bool isSimple = false);
  /** Set bound cache */
  static void setConstantBoundCache(TNode n, Node ret, bool isLower);
  /**
   * Get bound cache, store in c and return true if the bound for n has been
   * computed. Used for getConstantBound and getConstantBoundLength.
   */
  static bool getConstantBoundCache(TNode n, bool isLower, Node& c);
  /** The underlying rewriter, if one exists */
  Rewriter* d_rr;
  /** Whether we are using recursive arithmetic approximations */
  bool d_recApprox;
  /** Constant zero */
  Node d_zero;
  Node d_one;
  /** A cache for findApprox above */
  std::map<Node, Node> d_approxCache;
  /** A cache for findApprox above when isSimple is true */
  std::map<Node, Node> d_approxCacheSimple;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif
