/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements utilities for coverings projection operators.
 */

#include "theory/arith/nl/coverings/projections.h"

#ifdef CVC5_POLY_IMP

#include "base/check.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

using namespace poly;

void PolyVector::add(const poly::Polynomial& poly, bool assertMain)
{
  for (const auto& p : poly::square_free_factors(poly))
  {
    if (poly::is_constant(p)) continue;
    if (assertMain)
    {
      Assert(main_variable(poly) == main_variable(p));
    }
    std::vector<poly::Polynomial>::emplace_back(p);
  }
}

void PolyVector::reduce()
{
  std::sort(begin(), end());
  erase(std::unique(begin(), end()), end());
}

void PolyVector::makeFinestSquareFreeBasis()
{
  for (std::size_t i = 0, n = size(); i < n; ++i)
  {
    for (std::size_t j = i + 1; j < n; ++j)
    {
      Polynomial g = gcd((*this)[i], (*this)[j]);
      if (!is_constant(g))
      {
        (*this)[i] = div((*this)[i], g);
        (*this)[j] = div((*this)[j], g);
        add(g);
      }
    }
  }
  auto it = std::remove_if(
      begin(), end(), [](const Polynomial& p) { return is_constant(p); });
  erase(it, end());
  reduce();
}
void PolyVector::pushDownPolys(PolyVector& down, poly::Variable var)
{
  auto it =
      std::remove_if(begin(), end(), [&down, &var](const poly::Polynomial& p) {
        if (main_variable(p) == var) return false;
        down.add(p);
        return true;
      });
  erase(it, end());
}

PolyVector projectionMcCallum(const std::vector<Polynomial>& polys)
{
  PolyVector res;

  for (const auto& p : polys)
  {
    for (const auto& coeff : coefficients(p))
    {
      res.add(coeff);
    }
    res.add(discriminant(p));
  }
  for (std::size_t i = 0, n = polys.size(); i < n; ++i)
  {
    for (std::size_t j = i + 1; j < n; ++j)
    {
      res.add(resultant(polys[i], polys[j]));
    }
  }

  res.reduce();
  return res;
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
