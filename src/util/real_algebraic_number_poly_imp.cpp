/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
    : d_isRational(false), d_value(std::move(an))
{
}
#endif

RealAlgebraicNumber::RealAlgebraicNumber(const Integer& i)
    :
#ifdef CVC5_POLY_IMP
      d_isRational(true),
#endif
      d_rat(i)
{
}

RealAlgebraicNumber::RealAlgebraicNumber(const Rational& r)
    :
#ifdef CVC5_POLY_IMP
      d_isRational(true),
#endif
      d_rat(r)
{
}

RealAlgebraicNumber::RealAlgebraicNumber(const std::vector<long>& coefficients,
                                         long lower,
                                         long upper)
{
#ifdef CVC5_ASSERTIONS
  for (long c : coefficients)
  {
    Assert(std::numeric_limits<int32_t>::min() <= c
           && c <= std::numeric_limits<int32_t>::max())
        << "Coefficients need to fit within 32 bit integers. Please use the "
           "constructor based on Integer instead.";
  }
#endif
#ifdef CVC5_POLY_IMP
  d_isRational = false;
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
  d_isRational = false;
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
  d_isRational = false;
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
  if (!d_isRational)
  {
    return poly::is_rational(getValue());
  }
#endif
  return true;
}
Rational RealAlgebraicNumber::toRational() const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    return poly_utils::toRational(poly::to_rational_approximation(getValue()));
  }
#endif
  return getRationalValue();
}

std::string RealAlgebraicNumber::toString() const
{
  std::stringstream ss;
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    ss << getValue();
    return ss.str();
  }
#endif
  ss << getRationalValue();
  return ss.str();
}

#ifdef CVC5_POLY_IMP
poly::AlgebraicNumber RealAlgebraicNumber::convertToPoly(
    const RealAlgebraicNumber& r)
{
  // if we are already poly, just return the value
  if (!r.d_isRational)
  {
    return r.d_value;
  }
  // otherwise, this converts the rational value of r to poly
  const Rational& rr = r.getRationalValue();
  poly::Rational pr = poly_utils::toRational(rr);
  auto dr = poly_utils::toDyadicRational(rr);
  if (dr)
  {
    return poly::AlgebraicNumber(dr.value());
  }
  return poly::AlgebraicNumber(
      poly::UPolynomial({-numerator(pr), denominator(pr)}),
      poly::DyadicInterval(floor(pr), ceil(pr)));
}
#endif

bool RealAlgebraicNumber::operator==(const RealAlgebraicNumber& rhs) const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    return convertToPoly(*this) == convertToPoly(rhs);
  }
#endif
  return getRationalValue() == rhs.getRationalValue();
}
bool RealAlgebraicNumber::operator!=(const RealAlgebraicNumber& rhs) const
{
  return !(*this == rhs);
}
bool RealAlgebraicNumber::operator<(const RealAlgebraicNumber& rhs) const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    return convertToPoly(*this) < convertToPoly(rhs);
  }
#endif
  return getRationalValue() < rhs.getRationalValue();
}
bool RealAlgebraicNumber::operator<=(const RealAlgebraicNumber& rhs) const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    return convertToPoly(*this) <= convertToPoly(rhs);
  }
#endif
  return getRationalValue() <= rhs.getRationalValue();
}
bool RealAlgebraicNumber::operator>(const RealAlgebraicNumber& rhs) const
{
  return rhs < *this;
}
bool RealAlgebraicNumber::operator>=(const RealAlgebraicNumber& rhs) const
{
  return rhs <= *this;
  ;
}

RealAlgebraicNumber RealAlgebraicNumber::operator+(
    const RealAlgebraicNumber& rhs) const
{
#ifdef CVC5_POLY_IMP
  // if either is poly, we convert both and return the result
  if (!d_isRational || !rhs.d_isRational)
  {
    return convertToPoly(*this) + convertToPoly(rhs);
  }
#endif
  return getRationalValue() + rhs.getRationalValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator-(
    const RealAlgebraicNumber& rhs) const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    return convertToPoly(*this) - convertToPoly(rhs);
  }
#endif
  return getRationalValue() - rhs.getRationalValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator-() const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    return -getValue();
  }
#endif
  return -getRationalValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator*(
    const RealAlgebraicNumber& rhs) const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    return convertToPoly(*this) * convertToPoly(rhs);
  }
#endif
  return getRationalValue() * rhs.getRationalValue();
}
RealAlgebraicNumber RealAlgebraicNumber::operator/(
    const RealAlgebraicNumber& rhs) const
{
  Assert(!rhs.isZero()) << "Can not divide by zero";
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    return convertToPoly(*this) / convertToPoly(rhs);
  }
#endif
  return getRationalValue() / rhs.getRationalValue();
}

RealAlgebraicNumber& RealAlgebraicNumber::operator+=(
    const RealAlgebraicNumber& rhs)
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    getValue() = convertToPoly(*this) + convertToPoly(rhs);
    // ensure it is no longer marked as rational
    d_isRational = false;
    return *this;
  }
#endif
  getRationalValue() = getRationalValue() + rhs.getRationalValue();
  return *this;
}
RealAlgebraicNumber& RealAlgebraicNumber::operator-=(
    const RealAlgebraicNumber& rhs)
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    getValue() = convertToPoly(*this) - convertToPoly(rhs);
    // ensure it is no longer marked as rational
    d_isRational = false;
    return *this;
  }
#endif
  getRationalValue() = getRationalValue() - rhs.getRationalValue();
  return *this;
}
RealAlgebraicNumber& RealAlgebraicNumber::operator*=(
    const RealAlgebraicNumber& rhs)
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational || !rhs.d_isRational)
  {
    getValue() = convertToPoly(*this) * convertToPoly(rhs);
    // ensure it is no longer marked as rational
    d_isRational = false;
    return *this;
  }
#endif
  getRationalValue() = getRationalValue() * rhs.getRationalValue();
  return *this;
}

int RealAlgebraicNumber::sgn() const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    return poly::sgn(getValue());
  }
#endif
  return getRationalValue().sgn();
}
bool RealAlgebraicNumber::isZero() const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    return poly::is_zero(getValue());
  }
#endif
  return getRationalValue().isZero();
}
bool RealAlgebraicNumber::isOne() const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    return poly::is_one(getValue());
  }
#endif
  return getRationalValue().isOne();
}
RealAlgebraicNumber RealAlgebraicNumber::inverse() const
{
  Assert(!isZero()) << "Can not invert zero";
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    return poly::inverse(getValue());
  }
#endif
  return getRationalValue().inverse();
}

size_t RealAlgebraicNumber::hash() const
{
#ifdef CVC5_POLY_IMP
  if (!d_isRational)
  {
    return lp_algebraic_number_hash_approx(getValue().get_internal(), 2);
  }
#endif
  return getRationalValue().hash();
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
