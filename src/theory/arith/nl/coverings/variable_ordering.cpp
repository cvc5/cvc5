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
 * Implements variable orderings tailored to coverings.
 */

#include "theory/arith/nl/coverings/variable_ordering.h"

#ifdef CVC5_POLY_IMP

#include "util/poly_util.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

std::vector<poly_utils::VariableInformation> collectInformation(
    const Constraints::ConstraintVector& polys, bool with_totals)
{
  poly::VariableCollector vc;
  for (const auto& c : polys)
  {
    vc(std::get<0>(c));
  }
  std::vector<poly_utils::VariableInformation> res;
  for (const auto& v : vc.get_variables())
  {
    res.emplace_back();
    res.back().var = v;
    for (const auto& c : polys)
    {
      poly_utils::getVariableInformation(res.back(), std::get<0>(c));
    }
  }
  if (with_totals)
  {
    res.emplace_back();
    for (const auto& c : polys)
    {
      poly_utils::getVariableInformation(res.back(), std::get<0>(c));
    }
  }
  return res;
}

std::vector<poly::Variable> getVariables(
    const std::vector<poly_utils::VariableInformation>& vi)
{
  std::vector<poly::Variable> res;
  for (const auto& v : vi)
  {
    res.emplace_back(v.var);
  }
  return res;
}

std::vector<poly::Variable> sortByid(const Constraints::ConstraintVector& polys)
{
  auto vi = collectInformation(polys);
  std::sort(
      vi.begin(),
      vi.end(),
      [](const poly_utils::VariableInformation& a,
         const poly_utils::VariableInformation& b) { return a.var < b.var; });
  return getVariables(vi);
};

std::vector<poly::Variable> sortBrown(
    const Constraints::ConstraintVector& polys)
{
  auto vi = collectInformation(polys);
  std::sort(vi.begin(),
            vi.end(),
            [](const poly_utils::VariableInformation& a,
               const poly_utils::VariableInformation& b) {
              if (a.max_degree != b.max_degree)
                return a.max_degree > b.max_degree;
              if (a.max_terms_tdegree != b.max_terms_tdegree)
                return a.max_terms_tdegree > b.max_terms_tdegree;
              return a.num_terms > b.num_terms;
            });
  return getVariables(vi);
};

std::vector<poly::Variable> sortTriangular(
    const Constraints::ConstraintVector& polys)
{
  auto vi = collectInformation(polys);
  std::sort(vi.begin(),
            vi.end(),
            [](const poly_utils::VariableInformation& a,
               const poly_utils::VariableInformation& b) {
              if (a.max_degree != b.max_degree)
                return a.max_degree > b.max_degree;
              if (a.max_lc_degree != b.max_lc_degree)
                return a.max_lc_degree > b.max_lc_degree;
              return a.sum_poly_degree > b.sum_poly_degree;
            });
  return getVariables(vi);
};

VariableOrdering::VariableOrdering() {}
VariableOrdering::~VariableOrdering() {}

std::vector<poly::Variable> VariableOrdering::operator()(
    const Constraints::ConstraintVector& polys,
    VariableOrderingStrategy vos) const
{
  switch (vos)
  {
    case VariableOrderingStrategy::BYID: return sortByid(polys);
    case VariableOrderingStrategy::BROWN: return sortBrown(polys);
    case VariableOrderingStrategy::TRIANGULAR: return sortTriangular(polys);
    default: Assert(false) << "Unsupported variable ordering.";
  }
  return {};
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
