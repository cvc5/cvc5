#include "cvc4autoconfig.h"
#include "util/real_algebraic_number.h"

#ifndef CVC4_POLY_IMP  // Make sure this comes after cvc4autoconfig.h
#error "This source should only ever be built if CVC4_POLY_IMP is on !"
#endif /* CVC4_POLY_IMP */

#include <poly/polyxx.h>

#include "base/check.h"
#include "poly_util.h"

namespace CVC4 {

RealAlgebraicNumber::RealAlgebraicNumber(poly::AlgebraicNumber&& an)
    : d_value(std::move(an))
{
}

RealAlgebraicNumber::RealAlgebraicNumber(const Integer& i)
    : d_value(poly::DyadicRational(poly_utils::to_integer(i)))
{
}

RealAlgebraicNumber::RealAlgebraicNumber(const Rational& r)
{
  poly::Rational pr = poly_utils::to_rational(r);
  auto dr = poly_utils::to_dyadic_rational(r);
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

RealAlgebraicNumber::RealAlgebraicNumber(const std::vector<long>& coefficients, long lower, long upper)
    : d_value(poly::UPolynomial(coefficients), poly::DyadicInterval(lower, upper))
{
}

RealAlgebraicNumber::RealAlgebraicNumber(
    const std::vector<Integer>& coefficients,
    const Rational& lower,
    const Rational& upper)
{
  *this = poly_utils::to_ran_with_refinement(
      poly::UPolynomial(poly_utils::to_integer(coefficients)), lower, upper);
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
    coeffs.emplace_back(poly_utils::to_integer((c * factor).getNumerator()));
  }
  *this = poly_utils::to_ran_with_refinement(
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
bool is_zero(const RealAlgebraicNumber& ran) { return is_zero(ran.getValue()); }
bool is_one(const RealAlgebraicNumber& ran) { return is_one(ran.getValue()); }

}  // namespace CVC4
