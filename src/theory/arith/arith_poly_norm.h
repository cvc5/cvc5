/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utility for polynomial normalization
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__POLY_NORM_H
#define CVC5__THEORY__ARITH__POLY_NORM_H

#include <unordered_map>

#include "expr/node.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * A utility class for polynomial normalization. This is used by the proof
 * rule PfRule::ARITH_POLY_NORM.
 */
class PolyNorm
{
 public:
  /**
   * Add the monomial x*c to this polynomial.
   * If x is null, then x*c is treated as c.
   */
  void addMonomial(TNode x, const Rational& c, bool isNeg = false);
  /**
   * Multiply this polynomial by the monomial x*c, where c is a constant.
   * If x is null, then x*c is treated as c.
   */
  void multiplyMonomial(TNode x, const Rational& c);
  /** Add polynomial p to this one. */
  void add(const PolyNorm& p);
  /** Subtract polynomial p from this one. */
  void subtract(const PolyNorm& p);
  /** Multiply this polynomial by p */
  void multiply(const PolyNorm& p);
  /** Clear this polynomial */
  void clear();
  /** Return true if this polynomial is empty */
  bool empty() const;
  /** Is this polynomial equal to polynomial p? */
  bool isEqual(const PolyNorm& p) const;
  /**
   * Make polynomial from real term n. This method normalizes applications
   * of operators ADD, SUB, NEG, MULT, and NONLINEAR_MULT only.
   */
  static PolyNorm mkPolyNorm(TNode n);
  /** Do a and b normalize to the same polynomial? */
  static bool isArithPolyNorm(TNode a, TNode b);

 private:
  /**
   * Given two terms that are variables in monomials, return the
   * variable for the monomial when they are multiplied.
   */
  static Node multMonoVar(TNode m1, TNode m2);
  /** Get the list of variables whose product is m */
  static std::vector<TNode> getMonoVars(TNode m);
  /** The data, mapping monomial variables to coefficients */
  std::unordered_map<Node, Rational> d_polyNorm;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__POLY_NORM_H */
