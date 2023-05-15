/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generic utility to convert between libpoly polynomials and CoCoALib
 * polynomials.
 */

#include "theory/arith/nl/coverings/cocoa_converter.h"

#ifdef CVC5_POLY_IMP
#ifdef CVC5_USE_COCOA

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {
CoCoA::RingElem CoCoAConverter::operator()(const poly::UPolynomial& p,
                                           const poly::Variable& var,
                                           const CoCoA::ring& ring) const
{
  std::vector<poly::Integer> coeffs = poly::coefficients(p);
  CoCoA::RingElem res(ring);
  CoCoA::RingElem v = CoCoA::indet(ring, 0);
  CoCoA::RingElem mult(ring, 1);
  for (const auto& c : coeffs)
  {
    if (!poly::is_zero(c))
    {
      res += (*this)(c)*mult;
    }
    mult *= v;
  }
  Trace("nl-cov::cocoa") << "Converted " << p << " to " << res << std::endl;
  return res;
}

CoCoA::RingElem CoCoAConverter::operator()(const poly::Polynomial& q,
                                           const CoCoA::ring& ring) const
{
  CoCoAPolyConstructor cmd{*this, ring};
  // Do the actual conversion
  cmd.d_result = CoCoA::RingElem(ring);
  lp_polynomial_traverse_f f =
      [](const lp_polynomial_context_t* ctx, lp_monomial_t* m, void* data) {
        CoCoAPolyConstructor* d = static_cast<CoCoAPolyConstructor*>(data);
        CoCoA::BigInt coeff = (d->d_state)(*poly::detail::cast_from(&m->a));
        CoCoA::RingElem re(d->d_ring, coeff);
        for (size_t i = 0; i < m->n; ++i)
        {
          // variable exponent pair
          CoCoA::RingElem var = d->d_state.d_varPC.at(m->p[i].x);
          re *= CoCoA::power(var, m->p[i].d);
        }
        d->d_result += re;
      };
  lp_polynomial_traverse(q.get_internal(), f, &cmd);
  Trace("nl-cov::cocoa") << "Converted " << q << " to " << cmd.d_result
                         << std::endl;
  return cmd.d_result;
}

poly::Polynomial CoCoAConverter::convertImpl(const CoCoA::RingElem& p,
                                             poly::Integer& denominator) const
{
  denominator = poly::Integer(1);
  poly::Polynomial res;
  for (CoCoA::SparsePolyIter i = CoCoA::BeginIter(p); !CoCoA::IsEnded(i); ++i)
  {
    poly::Polynomial coeff;
    poly::Integer denom(1);
    CoCoA::BigRat numcoeff;
    if (CoCoA::IsRational(numcoeff, CoCoA::coeff(i)))
    {
      poly::Rational rat(mpq_class(CoCoA::mpqref(numcoeff)));
      denom = poly::denominator(rat);
      coeff = poly::numerator(rat);
    }
    else
    {
      coeff = convertImpl(CoCoA::CanonicalRepr(CoCoA::coeff(i)), denom);
    }
    if (!CoCoA::IsOne(CoCoA::PP(i)))
    {
      std::vector<long> exponents;
      CoCoA::exponents(exponents, CoCoA::PP(i));
      for (size_t vid = 0; vid < exponents.size(); ++vid)
      {
        if (exponents[vid] == 0) continue;
        const auto& ring = CoCoA::owner(p);
        poly::Variable v = d_varCP.at(std::make_pair(CoCoA::RingID(ring), vid));
        coeff *= poly::Polynomial(poly::Integer(1), v, exponents[vid]);
      }
    }
    if (denom != denominator)
    {
      poly::Integer g = gcd(denom, denominator);
      res = res * (denom / g) + coeff * (denominator / g);
      denominator *= (denom / g);
    }
    else
    {
      res += coeff;
    }
  }
  Trace("nl-cov::cocoa") << "Converted " << p << " to " << res << std::endl;
  return res;
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
#endif
