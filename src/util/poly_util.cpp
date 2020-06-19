#include "poly_util.h"

#include <poly/polyxx.h>

#include <map>

#include "base/check.h"
#include "maybe.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/real_algebraic_number.h"

namespace CVC4 {
namespace poly_utils {

/** Convert arbitrary data using a string as intermediary.
 * Assumes the existance of operator<<(std::ostream&, const From&) and To(const
 * std::string&); Should be the last resort for type conversions: it may not
 * only yield bad performance, but is also dependent on compatible string
 * representations. Use with care!
 */
template <typename To, typename From>
To cast_by_string(const From& f)
{
  std::stringstream s;
  s << f;
  return To(s.str());
}

Integer to_integer(const poly::Integer& i)
{
  const mpz_class& gi = *poly::detail::cast_to_gmp(&i);
#ifdef CVC4_GMP_IMP
  return Integer(gi);
#endif
#ifdef CVC4_CLN_IMP
  if (std::numeric_limits<long>::min() <= gi
      && gi <= std::numeric_limits<long>::max())
  {
    return Integer(gi.get_si());
  }
  else
  {
    return cast_by_string<Integer, poly::Integer>(i);
  }
#endif
}
Rational to_rational(const poly::Integer& i) { return Rational(to_integer(i)); }
Rational to_rational(const poly::Rational& r)
{
#ifdef CVC4_GMP_IMP
  return Rational(*poly::detail::cast_to_gmp(&r));
#endif
#ifdef CVC4_CLN_IMP
  return Rational(to_integer(numerator(r)), to_integer(denominator(r)));
#endif
}
Rational to_rational(const poly::DyadicRational& dr)
{
  return Rational(to_integer(numerator(dr)), to_integer(denominator(dr)));
}

poly::Integer to_integer(const Integer& i)
{
#ifdef CVC4_GMP_IMP
  return poly::Integer(i.getValue());
#endif
#ifdef CVC4_CLN_IMP
  if (std::numeric_limits<long>::min() <= i.getValue()
      && i.getValue() <= std::numeric_limits<long>::max())
  {
    return poly::Integer(cln::cl_I_to_long(i.getValue()));
  }
  else
  {
    return poly::Integer(cast_by_string<mpz_class, Integer>(i));
  }
#endif
}
std::vector<poly::Integer> to_integer(const std::vector<Integer>& vi)
{
  std::vector<poly::Integer> res;
  for (const auto& i : vi) res.emplace_back(to_integer(i));
  return res;
}
poly::Rational to_rational(const Rational& r)
{
#ifdef CVC4_GMP_IMP
  return poly::Rational(r.getValue());
#endif
#ifdef CVC4_CLN_IMP
  return poly::Rational(to_integer(r.getNumerator()),
                        to_integer(r.getDenominator()));
#endif
}

Maybe<poly::DyadicRational> to_dyadic_rational(const Rational& r)
{
  Integer den = r.getDenominator();
  if (den.isOne())
  {  // It's an integer anyway.
    return poly::DyadicRational(to_integer(r.getNumerator()));
  }
  unsigned long exp = den.isPow2();
  if (exp > 0)
  {
    // It's a dyadic rational.
    return div_2exp(poly::DyadicRational(to_integer(r.getNumerator())),
                    exp - 1);
  }
  return Maybe<poly::DyadicRational>();
}
Maybe<poly::DyadicRational> to_dyadic_rational(const poly::Rational& r)
{
  poly::Integer den = denominator(r);
  if (den == poly::Integer(1))
  {  // It's an integer anyway.
    return poly::DyadicRational(numerator(r));
  }
  // Use bit_size as an estimate for the dyadic exponent.
  unsigned long size = bit_size(den) - 1;
  if (mul_pow2(poly::Integer(1), size) == den)
  {
    // It's a dyadic rational.
    return div_2exp(poly::DyadicRational(numerator(r)), size);
  }
  return Maybe<poly::DyadicRational>();
}

void approximate_to_dyadic(poly::Rational& r, const poly::Rational& original)
{
  // Multiply both numerator and denominator by two.
  // Increase or decrease the numerator, depending on whether r is too small or
  // too large.
  poly::Integer n = mul_pow2(numerator(r), 1);
  if (r < original)
  {
    ++n;
  }
  else if (r > original)
  {
    --n;
  }
  r = poly::Rational(n, mul_pow2(denominator(r), 1));
}

poly::AlgebraicNumber to_poly_ran_with_refinement(poly::UPolynomial&& p,
                                                  const Rational& lower,
                                                  const Rational upper)
{
  Maybe<poly::DyadicRational> ml = to_dyadic_rational(lower);
  Maybe<poly::DyadicRational> mu = to_dyadic_rational(upper);
  if (ml && mu)
  {
    return poly::AlgebraicNumber(std::move(p),
                                 poly::DyadicInterval(ml.value(), mu.value()));
  }
  // The encoded real algebraic number did not have dyadic rational endpoints.
  poly::Rational origl = to_rational(lower);
  poly::Rational origu = to_rational(upper);
  poly::Rational l(floor(origl));
  poly::Rational u(ceil(origu));
  poly::RationalInterval ri(l, u);
  while (count_real_roots(p, ri) != 1)
  {
    approximate_to_dyadic(l, origl);
    approximate_to_dyadic(u, origu);
    ri = poly::RationalInterval(l, u);
  }
  Assert(count_real_roots(p, poly::RationalInterval(l, u)) == 1);
  ml = to_dyadic_rational(l);
  mu = to_dyadic_rational(u);
  Assert(ml && mu) << "Both bounds should be dyadic by now.";
  return poly::AlgebraicNumber(std::move(p),
                               poly::DyadicInterval(ml.value(), mu.value()));
}

RealAlgebraicNumber to_ran_with_refinement(poly::UPolynomial&& p,
                                           const Rational& lower,
                                           const Rational upper)
{
  return RealAlgebraicNumber(
      to_poly_ran_with_refinement(std::move(p), lower, upper));
}

}  // namespace poly_utils
}  // namespace CVC4
