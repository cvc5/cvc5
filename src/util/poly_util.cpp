/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for working with LibPoly.
 */

#include "poly_util.h"

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <map>
#include <sstream>

#include "base/check.h"
#include "maybe.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/real_algebraic_number.h"

namespace cvc5 {
namespace poly_utils {

namespace {
/**
 * Convert arbitrary data using a string as intermediary.
 * Assumes the existence of operator<<(std::ostream&, const From&) and To(const
 * std::string&); should be the last resort for type conversions: it may not
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
}  // namespace

Integer toInteger(const poly::Integer& i)
{
  const mpz_class& gi = *poly::detail::cast_to_gmp(&i);
#ifdef CVC5_GMP_IMP
  return Integer(gi);
#endif
#ifdef CVC5_CLN_IMP
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
Rational toRational(const poly::Integer& i) { return Rational(toInteger(i)); }
Rational toRational(const poly::Rational& r)
{
#ifdef CVC5_GMP_IMP
  return Rational(*poly::detail::cast_to_gmp(&r));
#endif
#ifdef CVC5_CLN_IMP
  return Rational(toInteger(numerator(r)), toInteger(denominator(r)));
#endif
}
Rational toRational(const poly::DyadicRational& dr)
{
  return Rational(toInteger(numerator(dr)), toInteger(denominator(dr)));
}
Rational toRationalAbove(const poly::Value& v)
{
  if (is_algebraic_number(v))
  {
    return toRational(get_upper_bound(as_algebraic_number(v)));
  }
  else if (is_dyadic_rational(v))
  {
    return toRational(as_dyadic_rational(v));
  }
  else if (is_integer(v))
  {
    return toRational(as_integer(v));
  }
  else if (is_rational(v))
  {
    return toRational(as_rational(v));
  }
  Assert(false) << "Can not convert " << v << " to rational.";
  return Rational();
}
Rational toRationalBelow(const poly::Value& v)
{
  if (is_algebraic_number(v))
  {
    return toRational(get_lower_bound(as_algebraic_number(v)));
  }
  else if (is_dyadic_rational(v))
  {
    return toRational(as_dyadic_rational(v));
  }
  else if (is_integer(v))
  {
    return toRational(as_integer(v));
  }
  else if (is_rational(v))
  {
    return toRational(as_rational(v));
  }
  Assert(false) << "Can not convert " << v << " to rational.";
  return Rational();
}

poly::Integer toInteger(const Integer& i)
{
#ifdef CVC5_GMP_IMP
  return poly::Integer(i.getValue());
#endif
#ifdef CVC5_CLN_IMP
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
std::vector<poly::Integer> toInteger(const std::vector<Integer>& vi)
{
  std::vector<poly::Integer> res;
  for (const auto& i : vi) res.emplace_back(toInteger(i));
  return res;
}
poly::Rational toRational(const Rational& r)
{
#ifdef CVC5_GMP_IMP
  return poly::Rational(r.getValue());
#endif
#ifdef CVC5_CLN_IMP
  return poly::Rational(toInteger(r.getNumerator()),
                        toInteger(r.getDenominator()));
#endif
}

Maybe<poly::DyadicRational> toDyadicRational(const Rational& r)
{
  Integer den = r.getDenominator();
  if (den.isOne())
  {  // It's an integer anyway.
    return poly::DyadicRational(toInteger(r.getNumerator()));
  }
  unsigned long exp = den.isPow2();
  if (exp > 0)
  {
    // It's a dyadic rational.
    return div_2exp(poly::DyadicRational(toInteger(r.getNumerator())), exp - 1);
  }
  return Maybe<poly::DyadicRational>();
}

Maybe<poly::DyadicRational> toDyadicRational(const poly::Rational& r)
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

poly::Rational approximateToDyadic(const poly::Rational& r,
                                   const poly::Rational& original)
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
  return poly::Rational(n, mul_pow2(denominator(r), 1));
}

poly::AlgebraicNumber toPolyRanWithRefinement(poly::UPolynomial&& p,
                                              const Rational& lower,
                                              const Rational& upper)
{
  Maybe<poly::DyadicRational> ml = toDyadicRational(lower);
  Maybe<poly::DyadicRational> mu = toDyadicRational(upper);
  if (ml && mu)
  {
    return poly::AlgebraicNumber(std::move(p),
                                 poly::DyadicInterval(ml.value(), mu.value()));
  }
  // The encoded real algebraic number did not have dyadic rational endpoints.
  poly::Rational origl = toRational(lower);
  poly::Rational origu = toRational(upper);
  poly::Rational l(floor(origl));
  poly::Rational u(ceil(origu));
  poly::RationalInterval ri(l, u);
  while (count_real_roots(p, ri) != 1)
  {
    l = approximateToDyadic(l, origl);
    u = approximateToDyadic(u, origu);
    ri = poly::RationalInterval(l, u);
  }
  Assert(count_real_roots(p, poly::RationalInterval(l, u)) == 1);
  ml = toDyadicRational(l);
  mu = toDyadicRational(u);
  Assert(ml && mu) << "Both bounds should be dyadic by now.";
  return poly::AlgebraicNumber(std::move(p),
                               poly::DyadicInterval(ml.value(), mu.value()));
}

RealAlgebraicNumber toRanWithRefinement(poly::UPolynomial&& p,
                                        const Rational& lower,
                                        const Rational& upper)
{
  return RealAlgebraicNumber(
      toPolyRanWithRefinement(std::move(p), lower, upper));
}

std::size_t totalDegree(const poly::Polynomial& p)
{
  std::size_t tdeg = 0;

  lp_polynomial_traverse_f f =
      [](const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* data) {
        std::size_t sum = 0;
        for (std::size_t i = 0; i < m->n; ++i)
        {
          sum += m->p[i].d;
        }

        std::size_t* td = static_cast<std::size_t*>(data);
        *td = std::max(*td, sum);
      };

  lp_polynomial_traverse(p.get_internal(), f, &tdeg);

  return tdeg;
}

std::ostream& operator<<(std::ostream& os, const VariableInformation& vi)
{
  if (vi.var == poly::Variable())
  {
    os << "Totals: ";
    os << "max deg " << vi.max_degree;
    os << ", sum term deg " << vi.sum_term_degree;
    os << ", sum poly deg " << vi.sum_poly_degree;
    os << ", num polys " << vi.num_polynomials;
    os << ", num terms " << vi.num_terms;
  }
  else
  {
    os << "Info for " << vi.var << ": ";
    os << "max deg " << vi.max_degree;
    os << ", max lc deg: " << vi.max_lc_degree;
    os << ", max term tdeg: " << vi.max_terms_tdegree;
    os << ", sum term deg " << vi.sum_term_degree;
    os << ", sum poly deg " << vi.sum_poly_degree;
    os << ", num polys " << vi.num_polynomials;
    os << ", num terms " << vi.num_terms;
  }
  return os;
}

struct GetVarInfo
{
  VariableInformation* info;
  std::size_t cur_var_degree = 0;
  std::size_t cur_lc_degree = 0;
};
void getVariableInformation(VariableInformation& vi,
                            const poly::Polynomial& poly)
{
  GetVarInfo varinfo;
  varinfo.info = &vi;
  lp_polynomial_traverse_f f =
      [](const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* data) {
        GetVarInfo* gvi = static_cast<GetVarInfo*>(data);
        VariableInformation* info = gvi->info;
        // Total degree of this term
        std::size_t tdeg = 0;
        // Degree of this variable within this term
        std::size_t vardeg = 0;
        for (std::size_t i = 0; i < m->n; ++i)
        {
          tdeg += m->p[i].d;
          if (m->p[i].x == info->var)
          {
            info->max_degree = std::max(info->max_degree, m->p[i].d);
            info->sum_term_degree += m->p[i].d;
            vardeg = m->p[i].d;
          }
        }
        if (info->var == poly::Variable())
        {
          ++info->num_terms;
          info->max_degree = std::max(info->max_degree, tdeg);
          info->sum_term_degree += tdeg;
        }
        else if (vardeg > 0)
        {
          ++info->num_terms;
          if (gvi->cur_var_degree < vardeg)
          {
            gvi->cur_lc_degree = tdeg - vardeg;
          }
          info->max_terms_tdegree = std::max(info->max_terms_tdegree, tdeg);
        }
      };
  std::size_t tmp_max_degree = vi.max_degree;
  std::size_t tmp_num_terms = vi.num_terms;
  vi.max_degree = 0;
  vi.num_terms = 0;
  lp_polynomial_traverse(poly.get_internal(), f, &varinfo);
  vi.max_lc_degree = std::max(vi.max_lc_degree, varinfo.cur_lc_degree);
  if (vi.num_terms > 0)
  {
    ++vi.num_polynomials;
  }
  vi.sum_poly_degree += vi.max_degree;
  vi.max_degree = std::max(vi.max_degree, tmp_max_degree);
  vi.num_terms += tmp_num_terms;
}

}  // namespace poly_utils
}  // namespace cvc5

#endif
