/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algebraic number constants; wraps a libpoly algebraic number.
 */

#include "cvc5_private.h"

#ifndef CVC5__REAL_ALGEBRAIC_NUMBER_H
#define CVC5__REAL_ALGEBRAIC_NUMBER_H

#include <vector>

#ifdef CVC5_POLY_IMP
#include <poly/polyxx.h>
#endif

#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {

class PolyConverter;

/**
 * Represents a real algebraic number based on poly::AlgebraicNumber.
 * This real algebraic number is represented by a (univariate) polynomial and an
 * isolating interval. The interval contains exactly one real root of the
 * polynomial, which is the number the real algebraic number as a whole
 * represents.
 * This representation can hold rationals (where the interval can be a point
 * interval and the polynomial is omitted), an irrational algebraic number (like
 * square roots), but no trancendentals (like pi).
 * Note that the interval representation uses dyadic rationals (denominators are
 * only powers of two).
 *
 * If libpoly is not available, this class serves as a wrapper around Rational
 * to allow using RealAlgebraicNumber, even if libpoly is not enabled.
 */
class RealAlgebraicNumber
{
  friend class PolyConverter;

 public:
  /** Construct as zero. */
  RealAlgebraicNumber() = default;
#ifdef CVC5_POLY_IMP
  /** Move from a poly::AlgebraicNumber type. */
  RealAlgebraicNumber(poly::AlgebraicNumber&& an);
#endif
  /** Copy from an Integer. */
  RealAlgebraicNumber(const Integer& i);
  /** Copy from a Rational. */
  RealAlgebraicNumber(const Rational& r);
  /**
   * Construct from a polynomial with the given coefficients and an open
   * interval with the given bounds.
   */
  RealAlgebraicNumber(const std::vector<long>& coefficients,
                      long lower,
                      long upper);
  /**
   * Construct from a polynomial with the given coefficients and an open
   * interval with the given bounds. If the bounds are not dyadic, we need to
   * perform refinement to find a suitable dyadic interval.
   * See poly_utils::toRanWithRefinement for more details.
   */
  RealAlgebraicNumber(const std::vector<Integer>& coefficients,
                      const Rational& lower,
                      const Rational& upper);
  /**
   * Construct from a polynomial with the given coefficients and an open
   * interval with the given bounds. If the bounds are not dyadic, we need to
   * perform refinement to find a suitable dyadic interval.
   * See poly_utils::toRanWithRefinement for more details.
   */
  RealAlgebraicNumber(const std::vector<Rational>& coefficients,
                      const Rational& lower,
                      const Rational& upper);

  /** Copy constructor. */
  RealAlgebraicNumber(const RealAlgebraicNumber& ran) = default;
  /** Move constructor. */
  RealAlgebraicNumber(RealAlgebraicNumber&& ran) = default;

  /** Default destructor. */
  ~RealAlgebraicNumber() = default;

  /** Copy assignment. */
  RealAlgebraicNumber& operator=(const RealAlgebraicNumber& ran) = default;
  /** Move assignment. */
  RealAlgebraicNumber& operator=(RealAlgebraicNumber&& ran) = default;

  /**
   * Check if this real algebraic number is actually rational.
   * If true, the value is rational and toRational() can safely be called.
   * If false, the value may still be rational, but was not recognized as
   * such yet.
   */
  bool isRational() const;
  /**
   * Returns the stored value as a rational.
   * The value is exact if isRational() returns true, otherwise it may only be a
   * rational approximation (of unknown precision).
   */
  Rational toRational() const;

  std::string toString() const;

  /** Compare two real algebraic numbers. */
  bool operator==(const RealAlgebraicNumber& rhs) const;
  /** Compare two real algebraic numbers. */
  bool operator!=(const RealAlgebraicNumber& rhs) const;
  /** Compare two real algebraic numbers. */
  bool operator<(const RealAlgebraicNumber& rhs) const;
  /** Compare two real algebraic numbers. */
  bool operator<=(const RealAlgebraicNumber& rhs) const;
  /** Compare two real algebraic numbers. */
  bool operator>(const RealAlgebraicNumber& rhs) const;
  /** Compare two real algebraic numbers. */
  bool operator>=(const RealAlgebraicNumber& rhs) const;

  /** Add two real algebraic numbers. */
  RealAlgebraicNumber operator+(const RealAlgebraicNumber& rhs) const;
  /** Subtract two real algebraic numbers. */
  RealAlgebraicNumber operator-(const RealAlgebraicNumber& rhs) const;
  /** Negate a real algebraic number. */
  RealAlgebraicNumber operator-() const;
  /** Multiply two real algebraic numbers. */
  RealAlgebraicNumber operator*(const RealAlgebraicNumber& rhs) const;
  /** Divide two real algebraic numbers. */
  RealAlgebraicNumber operator/(const RealAlgebraicNumber& rhs) const;

  /** Add and assign two real algebraic numbers. */
  RealAlgebraicNumber& operator+=(const RealAlgebraicNumber& rhs);
  /** Subtract and assign two real algebraic numbers. */
  RealAlgebraicNumber& operator-=(const RealAlgebraicNumber& rhs);
  /** Multiply and assign two real algebraic numbers. */
  RealAlgebraicNumber& operator*=(const RealAlgebraicNumber& rhs);

  /** Compute the sign of a real algebraic number. */
  int sgn() const;

  /** Check whether a real algebraic number is zero. */
  bool isZero() const;
  /** Check whether a real algebraic number is one. */
  bool isOne() const;
  /** Compute the inverse of a real algebraic number. */
  RealAlgebraicNumber inverse() const;
  /** Hash function */
  size_t hash() const;

 private:
#ifdef CVC5_POLY_IMP
  /** Get the internal value as a const reference. */
  const poly::AlgebraicNumber& getValue() const { return d_value; }
  /** Get the internal value as a non-const reference. */
  poly::AlgebraicNumber& getValue() { return d_value; }
  /**
   * Convert rational to poly, which returns d_value if it stores the
   * value of r, otherwise it converts and returns the rational value of r.
   */
  static poly::AlgebraicNumber convertToPoly(const RealAlgebraicNumber& r);
#endif
  /** Get the internal rational value as a const reference. */
  const Rational& getRationalValue() const { return d_rat; }
  /** Get the internal rational value as a non-const reference. */
  Rational& getRationalValue() { return d_rat; }
#ifdef CVC5_POLY_IMP
  /**
   * Whether the value of this real algebraic number is stored in d_rat.
   * Otherwise, it is stored in d_value.
   */
  bool d_isRational;
  /** Stores the actual real algebraic number, if applicable. */
  poly::AlgebraicNumber d_value;
#endif
  /** Stores the rational, if applicable. */
  Rational d_rat;
}; /* class RealAlgebraicNumber */

/** Stream a real algebraic number to an output stream. */
std::ostream& operator<<(std::ostream& os, const RealAlgebraicNumber& ran);

using RealAlgebraicNumberHashFunction = std::hash<RealAlgebraicNumber>;

}  // namespace cvc5::internal

namespace std {
template <>
struct hash<cvc5::internal::RealAlgebraicNumber>
{
  /**
   * Computes a hash of the given real algebraic number. Given that the internal
   * representation of real algebraic numbers are inherently mutable (th
   * interval may be refined for comparisons) we hash a well-defined rational
   * approximation.
   */
  size_t operator()(const cvc5::internal::RealAlgebraicNumber& ran) const;
};
}  // namespace std

#endif /* CVC5__REAL_ALGEBRAIC_NUMBER_H */
