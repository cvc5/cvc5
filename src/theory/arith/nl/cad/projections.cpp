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

#include "projections.h"

#ifdef CVC4_POLY_IMP

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

using namespace poly;

void reduce_projection_polynomials(std::vector<Polynomial>& polys)
{
  std::sort(polys.begin(), polys.end());
  auto it = std::unique(polys.begin(), polys.end());
  polys.erase(it, polys.end());
}

void add_polynomial(std::vector<Polynomial>& polys, const Polynomial& poly)
{
  for (const auto& p : square_free_factors(poly))
  {
    if (is_constant(p)) continue;
    polys.emplace_back(p);
  }
}

void add_polynomials(std::vector<Polynomial>& polys,
                     const std::vector<Polynomial>& p)
{
  for (const auto& q : p) add_polynomial(polys, q);
}

void make_finest_square_free_basis(std::vector<Polynomial>& polys)
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
  reduce_projection_polynomials(polys);
}

void make_finest_square_free_basis(std::vector<poly::Polynomial>& lhs,
                                   std::vector<poly::Polynomial>& rhs)
{
  for (std::size_t i = 0, ln = lhs.size(); i < ln; ++i)
  {
    for (std::size_t j = 0, rn = rhs.size(); j < rn; ++j)
    {
      if (lhs[i] == rhs[j]) continue;
      Polynomial g = gcd(lhs[i], rhs[j]);
      if (!is_constant(g))
      {
        lhs[i] = div(lhs[i], g);
        rhs[j] = div(rhs[j], g);
        lhs.emplace_back(g);
        rhs.emplace_back(g);
      }
    }
  }
  reduce_projection_polynomials(lhs);
  reduce_projection_polynomials(rhs);
}

std::vector<Polynomial> projection_mccallum(
    const std::vector<Polynomial>& polys)
{
  std::vector<Polynomial> res;

  for (const auto& p : polys)
  {
    for (const auto& coeff : coefficients(p))
    {
      add_polynomial(res, coeff);
    }
    add_polynomial(res, discriminant(p));
  }
  for (std::size_t i = 0, n = polys.size(); i < n; ++i)
  {
    for (std::size_t j = i + 1; j < n; ++j)
    {
      add_polynomial(res, resultant(polys[i], polys[j]));
    }
  }

  reduce_projection_polynomials(res);
  return res;
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
