/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
 * rule ProofRule::ARITH_POLY_NORM.
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
  /**
   * Modulus the coefficients of this polynomial by constant c, where c must be
   * integral.
   */
  void modCoeffs(const Rational& c);
  /** Clear this polynomial */
  void clear();
  /** Return true if this polynomial is empty */
  bool empty() const;
  /** Is this polynomial equal to polynomial p? */
  bool isEqual(const PolyNorm& p) const;
  /** Is this polynomial a constant? If so, store it in c */
  bool isConstant(Rational& c) const;
  /**
   * Is this polynomial equal to polynomial p*c for some c? If so, return
   * true and store in c.
   */
  bool isEqualMod(const PolyNorm& p, Rational& c) const;
  /**
   * Convert the polynomial representation to a node
   */
  Node toNode(const TypeNode& tn) const;
  /**
   * Make polynomial from real term n. This method normalizes applications
   * of operators ADD, SUB, NEG, MULT, NONLINEAR_MULT, bitvector equivalent
   * of these operators, and TO_REAL.
   */
  static PolyNorm mkPolyNorm(TNode n);
  /**
   * If a and b are atoms, do they normalize to atoms over the same
   * polynomial?
   * Otherwise, do a and b normalize to the same polynomial?
   */
  static bool isArithPolyNorm(TNode a, TNode b);
  /**
   * Do atoms a and b normalize to an atom over the same polynomial?
   * In particular, for relations a1 ~ a2 / b1 ~ b2, we return true
   * if the normalization of (a1-a2) is equivalent to the normalization of
   * (b1-b2).
   *
   * This method can return true if a/b are Int/Real and ~ is in {=,>=,>,<=,<}
   * or if a/b are bitvector and ~ is in {=}.
   */
  static bool isArithPolyNormAtom(TNode a, TNode b);

  /**
   * Return the normalized form of (arithmetic) term a based on the techniques
   * from this class.
   */
  static Node getPolyNorm(Node a);

 private:
  /**
   * Make the difference of two nodes a and b, independent of their type.
   */
  static PolyNorm mkDiff(TNode a, TNode b);
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
