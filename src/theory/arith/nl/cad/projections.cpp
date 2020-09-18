/*********************                                                        */
/*! \file projections.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements utilities for CAD projection operators.
 **
 ** Implements utilities for CAD projection operators.
 **/

#include "theory/arith/nl/cad/projections.h"

#ifdef CVC4_POLY_IMP

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

using namespace poly;

void reduceProjectionPolynomials(std::vector<Polynomial>& polys)
{
  std::sort(polys.begin(), polys.end());
  auto it = std::unique(polys.begin(), polys.end());
  polys.erase(it, polys.end());
}

void addPolynomial(std::vector<Polynomial>& polys, const Polynomial& poly)
{
  for (const auto& p : square_free_factors(poly))
  {
    if (is_constant(p)) continue;
    polys.emplace_back(p);
  }
}

void addPolynomials(std::vector<Polynomial>& polys,
                    const std::vector<Polynomial>& p)
{
  for (const auto& q : p) addPolynomial(polys, q);
}

void makeFinestSquareFreeBasis(std::vector<Polynomial>& polys)
{
  for (std::size_t i = 0, n = polys.size(); i < n; ++i)
  {
    for (std::size_t j = i + 1; j < n; ++j)
    {
      Polynomial g = gcd(polys[i], polys[j]);
      if (!is_constant(g))
      {
        polys[i] = div(polys[i], g);
        polys[j] = div(polys[j], g);
        polys.emplace_back(g);
      }
    }
  }
  auto it = std::remove_if(polys.begin(), polys.end(), [](const Polynomial& p) {
    return is_constant(p);
  });
  polys.erase(it, polys.end());
  reduceProjectionPolynomials(polys);
}

std::vector<Polynomial> projection_mccallum(
    const std::vector<Polynomial>& polys)
{
  std::vector<Polynomial> res;

  for (const auto& p : polys)
  {
    for (const auto& coeff : coefficients(p))
    {
      addPolynomial(res, coeff);
    }
    addPolynomial(res, discriminant(p));
  }
  for (std::size_t i = 0, n = polys.size(); i < n; ++i)
  {
    for (std::size_t j = i + 1; j < n; ++j)
    {
      addPolynomial(res, resultant(polys[i], polys[j]));
    }
  }

  reduceProjectionPolynomials(res);
  return res;
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
