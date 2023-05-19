/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  ArithEntail(Rewriter* r);
  /**
   * Returns the rewritten form a term, intended (although not enforced) to be
   * an arithmetic term.
   */
  Node rewrite(Node a);
  /** check arithmetic entailment equal
   * Returns true if it is always the case that a = b.
   */
  bool checkEq(Node a, Node b);
  /** check arithmetic entailment
   * Returns true if it is always the case that a >= b,
   * and a>b if strict is true.
   */
  bool check(Node a, Node b, bool strict = false);
  /** check arithmetic entailment
   * Returns true if it is always the case that a >= 0.
   */
  bool check(Node a, bool strict = false);
  /** check arithmetic entailment with approximations
   *
   * Returns true if it is always the case that a >= 0. We expect that a is in
   * rewritten form.
   *
   * This function uses "approximation" techniques that under-approximate
   * the value of a for the purposes of showing the entailment holds. For
   * example, given:
   *   len( x ) - len( substr( y, 0, len( x ) ) )
   * Since we know that len( substr( y, 0, len( x ) ) ) <= len( x ), the above
   * term can be under-approximated as len( x ) - len( x ) = 0, which is >= 0,
   * and thus the entailment len( x ) - len( substr( y, 0, len( x ) ) ) >= 0
   * holds.
   */
  bool checkApprox(Node a);

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

 private:
  /** check entail arithmetic internal
   * Returns true if we can show a >= 0 always.
   * a is in rewritten form.
   */
  bool checkInternal(Node a);
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
                              bool isOverApprox = false);
  /** Set bound cache */
  static void setConstantBoundCache(TNode n, Node ret, bool isLower);
  /**
   * Get bound cache, store in c and return true if the bound for n has been
   * computed. Used for getConstantBound and getConstantBoundLength.
   */
  static bool getConstantBoundCache(TNode n, bool isLower, Node& c);
  /** The underlying rewriter */
  Rewriter* d_rr;
  /** Constant zero */
  Node d_zero;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif
