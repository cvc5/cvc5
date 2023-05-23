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
 * Implements a container for coverings constraints.
 */

#include "theory/arith/nl/coverings/constraints.h"

#ifdef CVC5_POLY_IMP

#include <algorithm>

#include "theory/arith/nl/poly_conversion.h"
#include "util/poly_util.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

void Constraints::addConstraint(const poly::Polynomial& lhs,
                                poly::SignCondition sc,
                                Node n)
{
  d_constraints.emplace_back(lhs, sc, n);
  sortConstraints();
}

void Constraints::addConstraint(Node n)
{
  auto c = as_poly_constraint(n, d_varMapper);
  addConstraint(c.first, c.second, n);
  sortConstraints();
}

const Constraints::ConstraintVector& Constraints::getConstraints() const
{
  return d_constraints;
}

void Constraints::reset() { d_constraints.clear(); }

void Constraints::sortConstraints()
{
  using Tpl = std::tuple<poly::Polynomial, poly::SignCondition, Node>;
  std::sort(d_constraints.begin(),
            d_constraints.end(),
            [](const Tpl& at, const Tpl& bt) {
              // Check if a is smaller than b
              const poly::Polynomial& a = std::get<0>(at);
              const poly::Polynomial& b = std::get<0>(bt);
              bool ua = is_univariate(a);
              bool ub = is_univariate(b);
              if (ua != ub) return ua;
              std::size_t tda = poly_utils::totalDegree(a);
              std::size_t tdb = poly_utils::totalDegree(b);
              if (tda != tdb) return tda < tdb;
              return degree(a) < degree(b);
            });
  for (auto& c : d_constraints)
  {
    auto* p = std::get<0>(c).get_internal();
    lp_polynomial_set_external(p);
  }
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
