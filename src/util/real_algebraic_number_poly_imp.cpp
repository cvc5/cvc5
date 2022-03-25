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
 * Implementation of RealAlgebraicNumber based on libpoly.
 */

#include "base/cvc5config.h"
#include "util/real_algebraic_number.h"

#ifdef CVC5_POLY_IMP
#include <poly/polyxx.h>
#endif

#include <limits>

#include "base/check.h"
#include "util/poly_util.h"

#define RAN_UNREACHABLE \
  Unreachable() << "RealAlgebraicNumber is not available without libpoly."

namespace cvc5 {

#ifdef CVC5_POLY_IMP
RealAlgebraicNumber::RealAlgebraicNumber(poly::AlgebraicNumber&& an)
    : d_value(std::move(an))
{
}
#endif

RealAlgebraicNumber::RealAlgebraicNumber(const Integer& i)
#ifdef CVC5_POLY_IMP
    : d_value(poly::DyadicRational(poly_utils::toInteger(i)))
#else
    : d_value(i)
#endif
{
}

RealAlgebraicNumber::RealAlgebraicNumber(const Rational& r)
#ifndef CVC5_POLY_IMP
    : d_value(r)
#endif
{
#ifdef CVC5_POLY_IMP
  poly::Rational pr = poly_utils::toRational(r);
  auto dr = poly_utils::toDyadicRational(r);
  if (dr)
  {
    d_value = poly::AlgebraicNumber(dr.value());
  }
  else
  {
    d_value = poly::AlgebraicNumber(
        poly::UPolynomial({-numerator(pr), denominator(pr)}),
        poly::DyadicInterval(floor(pr), ceil(pr)));
  }
#endif
}

RealAlgebraicNumber::RealAlgebraicNumber(const std::vector<long>& coefficients,
                                         long lower,
                                         long upper)
{
#ifdef CVC5_ASSERTIONS
  for (long c : coefficients)
  {
    Assert(std::numeric_limits<std::int32_t>::min() <= c
           && c <= std::numeric_limits<std::int32_t>::max())
        << "Coefficients need to fit within 32 bit integers. Please use the "
           "constructor based on Integer instead.";
  }
#endif
#ifdef CVC5_POLY_IMP
  d_value = poly::AlgebraicNumber(poly::UPolynomial(coefficients),
                                  poly::DyadicInterval(lower, upper));
#else
  RAN_UNREACHABLE;
#endif
}

RealAlgebraicNumber::RealAlgebraicNumber(
    const std::vector<Integer>& coefficients,
    const Rational& lower,
    const Rational& upper)
{
#ifdef CVC5_POLY_IMP
  *this = poly_utils::toRanWithRefinement(
      poly::UPolynomial(poly_utils::toInteger(coefficients)), lower, upper);
#else
  RAN_UNREACHABLE;
#endif
}
RealAlgebraicNumber::RealAlgebraicNumber(
    const std::vector<Rational>& coefficients,
    const Rational& lower,
    const Rational& upper)
{
#ifdef CVC5_POLY_IMP
  Integer factor = Integer(1);
  for (const auto& c : coefficients)
  {
    factor = factor.lcm(c.getDenominator());
  }
  std::vector<poly::Integer> coeffs;
  for (const auto& c : coefficients)
  {
    Assert((c * factor).getDenominator() == Integer(1));
    coeffs.emplace_back(poly_utils::toInteger((c * factor).getNumerator()));
  }
  *this = poly_utils::toRanWithRefinement(
      poly::UPolynomial(std::move(coeffs)), lower, upper);
#else
  RAN_UNREACHABLE;
#endif
}

bool RealAlgebraicNumber::isRational() const
{
#ifdef CVC5_POLY_IMP
  return poly::is_rational(getValue());
#else
  return true;
#endif
}
Rational RealAlgebraicNumber::toRational() const
{
#ifdef CVC5_POLY_IMP
  return poly_utils::toRational(poly::to_rational_approximation(getValue()));
#else
  return d_value;
#endif
}

std::ostream& operator<<(std::ostream& os, const RealAlgebraicNumber& ran)
{
  return os << ran.getValue();
}

bool operator==(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() == rhs.getValue();
}
bool operator!=(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() != rhs.getValue();
}
bool operator<(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() < rhs.getValue();
}
bool operator<=(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() <= rhs.getValue();
}
bool operator>(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() > rhs.getValue();
}
bool operator>=(const RealAlgebraicNumber& lhs, const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() >= rhs.getValue();
}

RealAlgebraicNumber operator+(const RealAlgebraicNumber& lhs,
                              const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() + rhs.getValue();
}
RealAlgebraicNumber operator-(const RealAlgebraicNumber& lhs,
                              const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() - rhs.getValue();
}
RealAlgebraicNumber operator-(const RealAlgebraicNumber& ran)
{
  return -ran.getValue();
}
RealAlgebraicNumber operator*(const RealAlgebraicNumber& lhs,
                              const RealAlgebraicNumber& rhs)
{
  return lhs.getValue() * rhs.getValue();
}
RealAlgebraicNumber operator/(const RealAlgebraicNumber& lhs,
                              const RealAlgebraicNumber& rhs)
{
  Assert(!isZero(rhs)) << "Can not divide by zero";
  return lhs.getValue() / rhs.getValue();
}

RealAlgebraicNumber& operator+=(RealAlgebraicNumber& lhs,
                                const RealAlgebraicNumber& rhs)
{
  lhs.getValue() = lhs.getValue() + rhs.getValue();
  return lhs;
}
RealAlgebraicNumber& operator-=(RealAlgebraicNumber& lhs,
                                const RealAlgebraicNumber& rhs)
{
  lhs.getValue() = lhs.getValue() - rhs.getValue();
  return lhs;
}
RealAlgebraicNumber& operator*=(RealAlgebraicNumber& lhs,
                                const RealAlgebraicNumber& rhs)
{
  lhs.getValue() = lhs.getValue() * rhs.getValue();
  return lhs;
}

int sgn(const RealAlgebraicNumber& ran) {
#ifdef CVC5_POLY_IMP
  return sgn(ran.getValue());
#else
  return ran.getValue().sgn();
#endif
}
bool isZero(const RealAlgebraicNumber& ran) {
#ifdef CVC5_POLY_IMP
  return is_zero(ran.getValue());
#else
  return ran.getValue().isZero();
#endif
}
bool isOne(const RealAlgebraicNumber& ran) {
#ifdef CVC5_POLY_IMP
  return is_one(ran.getValue());
#else
  return ran.getValue().isOne();
#endif
}
RealAlgebraicNumber inverse(const RealAlgebraicNumber& ran)
{
  Assert(!isZero(ran)) << "Can not invert zero";
#ifdef CVC5_POLY_IMP
  return inverse(ran.getValue());
#else
  return ran.getValue().inverse();
#endif
}

}  // namespace cvc5

namespace std {
size_t hash<cvc5::RealAlgebraicNumber>::operator()(
    const cvc5::RealAlgebraicNumber& ran) const
{
#ifdef CVC5_POLY_IMP
  return lp_algebraic_number_hash_approx(ran.getValue().get_internal(), 2);
#else
  return ran.getValue().hash();
#endif
}
}  // namespace std
