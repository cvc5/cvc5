/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include <poly/polyxx.h>

#include "util/integer.h"
#include "util/rational.h"

namespace cvc5 {

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
 */
class RealAlgebraicNumber
{
 public:
  /** Construct as zero. */
  RealAlgebraicNumber() = default;
  /** Move from a poly::AlgebraicNumber type. */
  RealAlgebraicNumber(poly::AlgebraicNumber&& an);
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

  /** Get the internal value as a const reference. */
  const poly::AlgebraicNumber& getValue() const { return d_value; }
  /** Get the internal value as a non-const reference. */
  poly::AlgebraicNumber& getValue() { return d_value; }

 private:
  /**
   * Stores the actual real algebraic number.
   */
  poly::AlgebraicNumber d_value;
}; /* class RealAlgebraicNumber */

/** Stream a real algebraic number to an output stream. */
std::ostream& operator<<(std::ostream& os, const RealAlgebraicNumber& ran);

/** Compare two real algebraic numbers. */
bool operator==(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs);
/** Compare two real algebraic numbers. */
bool operator!=(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs);
/** Compare two real algebraic numbers. */
bool operator<(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs);
/** Compare two real algebraic numbers. */
bool operator<=(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs);
/** Compare two real algebraic numbers. */
bool operator>(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs);
/** Compare two real algebraic numbers. */
bool operator>=(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs);

/** Add two real algebraic numbers. */
RealAlgebraicNumber operator+(const RealAlgebraicNumber& lhs,
                              const RealAlgebraicNumber& rhs);
/** Subtract two real algebraic numbers. */
RealAlgebraicNumber operator-(const RealAlgebraicNumber& lhs,
                              const RealAlgebraicNumber& rhs);
/** Negate a real algebraic number. */
RealAlgebraicNumber operator-(const RealAlgebraicNumber& ran);
/** Multiply two real algebraic numbers. */
RealAlgebraicNumber operator*(const RealAlgebraicNumber& lhs,
                              const RealAlgebraicNumber& rhs);

/** Add and assign two real algebraic numbers. */
RealAlgebraicNumber& operator+=(RealAlgebraicNumber& lhs,
                                const RealAlgebraicNumber& rhs);
/** Subtract and assign two real algebraic numbers. */
RealAlgebraicNumber& operator-=(RealAlgebraicNumber& lhs,
                                const RealAlgebraicNumber& rhs);
/** Multiply and assign two real algebraic numbers. */
RealAlgebraicNumber& operator*=(RealAlgebraicNumber& lhs,
                                const RealAlgebraicNumber& rhs);

/** Compute the sign of a real algebraic number. */
int sgn(const RealAlgebraicNumber& ran);

/** Check whether a real algebraic number is zero. */
bool isZero(const RealAlgebraicNumber& ran);
/** Check whether a real algebraic number is one. */
bool isOne(const RealAlgebraicNumber& ran);

}  // namespace cvc5

#endif /* CVC5__REAL_ALGEBRAIC_NUMBER_H */
