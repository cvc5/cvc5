#include "constraints.h"

#include <algorithm>

#include "../poly_conversion.h"
#include "util/poly_util.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

using namespace poly;

void Constraints::sort_constraints()
{
  using Tpl = std::tuple<poly::Polynomial, poly::SignCondition, Node>;
  std::sort(mConstraints.begin(),
            mConstraints.end(),
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
  for (auto& c : mConstraints)
  {
    auto* p = std::get<0>(c).get_internal();
    lp_polynomial_set_external(p);
  }
}

void Constraints::add_constraint(const Polynomial& lhs,
                                 SignCondition sc,
                                 Node n)
{
  mConstraints.emplace_back(lhs, sc, n);
  sort_constraints();
}

void Constraints::add_constraint(Node n)
{
  auto c = as_poly_constraint(n, mVarMapper);
  add_constraint(c.first, c.second, n);
  sort_constraints();
}

const Constraints::ConstraintVector& Constraints::get_constraints() const
{
  return mConstraints;
}

void Constraints::reset() { mConstraints.clear(); }

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
