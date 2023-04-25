/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
#include <sstream>

#include "base/check.h"
#include "util/poly_util.h"

#define RAN_UNREACHABLE \
  Unreachable() << "RealAlgebraicNumber is not available without libpoly."

namespace cvc5::internal {

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

std::string RealAlgebraicNumber::toString() const
{
  std::stringstream ss;
  ss << getValue();
  return ss.str();
}

bool RealAlgebraicNumber::operator==(const RealAlgebraicNumber& rhs) const
{
  return getValue() == rhs.getValue();
}
bool RealAlgebraicNumber::operator!=(const RealAlgebraicNumber& rhs) const
{
  return getValue() != rhs.getValue();
}
bool RealAlgebraicNumber::operator<(const RealAlgebraicNumber& rhs) const
{
  return getValue() < rhs.getValue();
}
bool RealAlgebraicNumber::operator<=(const RealAlgebraicNumber& rhs) const
{
  return getValue() <= rhs.getValue();
}
bool RealAlgebraicNumber::operator>(const RealAlgebraicNumber& rhs) const
{
  return getValue() > rhs.getValue();
}
bool RealAlgebraicNumber::operator>=(const RealAlgebraicNumber& rhs) const
{
  return getValue() >= rhs.getValue();
}

RealAlgebraicNumber RealAlgebraicNumber::operator+(
    const RealAlgebraicNumber& rhs) const
{
  return getValue() + rhs.getValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator-(
    const RealAlgebraicNumber& rhs) const
{
  return getValue() - rhs.getValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator-() const
{
  return -getValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator*(
    const RealAlgebraicNumber& rhs) const
{
  return getValue() * rhs.getValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator/(
    const RealAlgebraicNumber& rhs) const
{
  Assert(!isZero(rhs)) << "Can not divide by zero";
  return getValue() / rhs.getValue();
}

RealAlgebraicNumber& RealAlgebraicNumber::operator+=(
    const RealAlgebraicNumber& rhs)
{
  getValue() = getValue() + rhs.getValue();
  return *this;
}
RealAlgebraicNumber& RealAlgebraicNumber::operator-=(
    const RealAlgebraicNumber& rhs)
{
  getValue() = getValue() - rhs.getValue();
  return *this;
}
RealAlgebraicNumber& RealAlgebraicNumber::operator*=(
    const RealAlgebraicNumber& rhs)
{
  getValue() = getValue() * rhs.getValue();
  return *this;
}

int RealAlgebraicNumber::sgn() const
{
#ifdef CVC5_POLY_IMP
  return poly::sgn(getValue());
#else
  return getValue().sgn();
#endif
}
bool RealAlgebraicNumber::isZero() const
{
#ifdef CVC5_POLY_IMP
  return poly::is_zero(getValue());
#else
  return getValue().isZero();
#endif
}
bool RealAlgebraicNumber::isOne() const
{
#ifdef CVC5_POLY_IMP
  return poly::is_one(getValue());
#else
  return getValue().isOne();
#endif
}
RealAlgebraicNumber RealAlgebraicNumber::inverse() const
{
  Assert(!isZero(ran)) << "Can not invert zero";
#ifdef CVC5_POLY_IMP
  return poly::inverse(getValue());
#else
  return getValue().inverse();
#endif
}

size_t RealAlgebraicNumber::hash() const
{
#ifdef CVC5_POLY_IMP
  return lp_algebraic_number_hash_approx(getValue().get_internal(), 2);
#else
  return getValue().hash();
#endif
}

std::ostream& operator<<(std::ostream& os, const RealAlgebraicNumber& ran)
{
  return os << ran.toString();
}

}  // namespace cvc5::internal

namespace std {
size_t hash<cvc5::internal::RealAlgebraicNumber>::operator()(
    const cvc5::internal::RealAlgebraicNumber& ran) const
{
  return ran.hash();
}

}  // namespace std
