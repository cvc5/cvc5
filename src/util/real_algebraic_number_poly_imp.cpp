/*********************                                                        */
/*! \file real_algebraic_number_poly_imp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of RealAlgebraicNumber based on libpoly.
 **
 ** Implementation of RealAlgebraicNumber based on libpoly.
 **/

#include "cvc4autoconfig.h"
#include "util/real_algebraic_number.h"

#ifndef CVC4_POLY_IMP  // Make sure this comes after cvc4autoconfig.h
#error "This source should only ever be built if CVC4_POLY_IMP is on!"
#endif /* CVC4_POLY_IMP */

#include <poly/polyxx.h>

#include <limits>

#include "base/check.h"
#include "util/poly_util.h"

namespace CVC4 {

RealAlgebraicNumber::RealAlgebraicNumber(poly::AlgebraicNumber&& an)
    : d_value(std::move(an))
{
}

RealAlgebraicNumber::RealAlgebraicNumber(const Integer& i)
    : d_value(poly::DyadicRational(poly_utils::toInteger(i)))
{
}

RealAlgebraicNumber::RealAlgebraicNumber(const Rational& r)
{
  poly::Rational pr = poly_utils::toRational(r);
  auto dr = poly_utils::toDyadicRational(r);
  if (dr)
  {
    d_value = poly::AlgebraicNumber(dr.value());
  }
  else
  {
    d_value = poly::AlgebraicNumber(
        poly::UPolynomial({numerator(pr), -denominator(pr)}),
        poly::DyadicInterval(floor(pr), ceil(pr)));
  }
}

RealAlgebraicNumber::RealAlgebraicNumber(const std::vector<long>& coefficients,
                                         long lower,
                                         long upper)
{
  for (long c : coefficients)
  {
    Assert(std::numeric_limits<std::int32_t>::min() <= c
           && c <= std::numeric_limits<std::int32_t>::max())
        << "Coefficients need to fit within 32 bit integers. Please use the "
           "constructor based on Integer instead.";
  }
  d_value = poly::AlgebraicNumber(poly::UPolynomial(coefficients),
                                  poly::DyadicInterval(lower, upper));
}

RealAlgebraicNumber::RealAlgebraicNumber(
    const std::vector<Integer>& coefficients,
    const Rational& lower,
    const Rational& upper)
{
  *this = poly_utils::toRanWithRefinement(
      poly::UPolynomial(poly_utils::toInteger(coefficients)), lower, upper);
}
RealAlgebraicNumber::RealAlgebraicNumber(
    const std::vector<Rational>& coefficients,
    const Rational& lower,
    const Rational& upper)
{
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

int sgn(const RealAlgebraicNumber& ran) { return sgn(ran.getValue()); }
bool isZero(const RealAlgebraicNumber& ran) { return is_zero(ran.getValue()); }
bool isOne(const RealAlgebraicNumber& ran) { return is_one(ran.getValue()); }

}  // namespace CVC4
