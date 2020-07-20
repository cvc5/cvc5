/*********************                                                        */
/*! \file cdcac.cpp
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
 ** \brief Implements the CDCAC approach.
 **
 ** Implements the CDCAC approach as described in
 ** https://arxiv.org/pdf/2003.05633.pdf.
 **/

#include "cdcac.h"

#include "projections.h"
#include "variable_ordering.h"

namespace std {
/** Generic streaming operator for std::vector. */
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v)
{
  CVC4::container_to_stream(os, v);
  return os;
}
}  // namespace std

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

namespace {
/** Removed duplicates from a vector. */
template <typename T>
void remove_duplicates(std::vector<T>& v)
{
  std::sort(v.begin(), v.end());
  v.erase(std::unique(v.begin(), v.end()), v.end());
}
}  // namespace

CDCAC::CDCAC() {}

CDCAC::CDCAC(const std::vector<Variable>& ordering)
    : mVariableOrdering(ordering)
{
}

void CDCAC::reset()
{
  mConstraints.reset();
  mAssignment.clear();
}

void CDCAC::compute_variable_ordering()
{
  // Actually compute the variable ordering
  mVariableOrdering = mVarOrder(mConstraints.get_constraints(),
                                VariableOrderingStrategy::BROWN);
  Trace("cdcac") << "Variable ordering is now " << mVariableOrdering
                 << std::endl;

  // Write variable ordering back to libpoly.
  lp_variable_order_t* vo = poly::Context::get_context().get_variable_order();
  lp_variable_order_clear(vo);
  for (const auto& v : mVariableOrdering)
  {
    lp_variable_order_push(vo, v.get_internal());
  }
}

Constraints& CDCAC::get_constraints() { return mConstraints; }
const Constraints& CDCAC::get_constraints() const { return mConstraints; }

const Assignment& CDCAC::get_model() const { return mAssignment; }

const std::vector<Variable>& CDCAC::get_variable_ordering() const
{
  return mVariableOrdering;
}

std::vector<CACInterval> CDCAC::get_unsat_intervals(
    std::size_t cur_variable) const
{
  std::vector<CACInterval> res;
  for (const auto& c : mConstraints.get_constraints())
  {
    const Polynomial& p = std::get<0>(c);
    SignCondition sc = std::get<1>(c);
    const Node& n = std::get<2>(c);

    if (main_variable(p) != mVariableOrdering[cur_variable])
    {
      // Constraint is in another variable, ignore it.
      continue;
    }

    Trace("cdcac") << "Infeasible intervals for " << p << " " << sc
                   << " 0 over " << mAssignment << std::endl;
    auto intervals = infeasible_regions(p, mAssignment, sc);
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i << std::endl;
      std::vector<Polynomial> l, u, m, d;
      // TODO(Gereon): Factorize polynomials here.
      if (!is_minus_infinity(get_lower(i))) l.emplace_back(p);
      if (!is_plus_infinity(get_upper(i))) u.emplace_back(p);
      m.emplace_back(p);
      res.emplace_back(CACInterval{i, l, u, m, d, {n}});
    }
  }
  clean_intervals(res);
  return res;
}

std::vector<Polynomial> CDCAC::required_coefficients(const Polynomial& p) const
{
  std::vector<Polynomial> res;
  for (long deg = degree(p); deg >= 0; --deg)
  {
    auto coeff = coefficient(p, deg);
    if (lp_polynomial_is_constant(coeff.get_internal())) break;
    res.emplace_back(coeff);
    if (evaluate_constraint(coeff, mAssignment, SignCondition::NE))
    {
      break;
    }
  }
  return res;
}

std::vector<Polynomial> CDCAC::construct_characterization(
    std::vector<CACInterval>& intervals)
{
  Assert(!intervals.empty()) << "A covering can not be empty";
  Trace("cdcac") << "Constructing characterization now" << std::endl;
  std::vector<Polynomial> res;

  for (const auto& i : intervals)
  {
    Trace("cdcac") << "Considering " << i.mInterval << std::endl;
    Trace("cdcac") << "-> " << i.mLowerPolys << " / " << i.mUpperPolys
                   << " and " << i.mMainPolys << " / " << i.mDownPolys
                   << std::endl;
    Trace("cdcac") << "-> " << i.mOrigins << std::endl;
    for (const auto& p : i.mDownPolys)
    {
      // Add all polynomial from lower levels.
      add_polynomial(res, p);
    }
    for (const auto& p : i.mMainPolys)
    {
      Trace("cdcac") << "Discriminant of " << p << " -> " << discriminant(p)
                     << std::endl;
      // Add all discriminants
      add_polynomial(res, discriminant(p));

      for (const auto& q : required_coefficients(p))
      {
        // Add all required coefficients
        Trace("cdcac") << "Coeff of " << p << " -> " << q << std::endl;
        add_polynomial(res, q);
      }
      // TODO(Gereon): Only add if p(s \times a) = a for some a <= l
      for (const auto& q : i.mLowerPolys)
      {
        if (p == q) continue;
        Trace("cdcac") << "Resultant of " << p << " and " << q << " -> "
                       << resultant(p, q) << std::endl;
        add_polynomial(res, resultant(p, q));
      }
      // TODO(Gereon): Only add if p(s \times a) = a for some a >= u
      for (const auto& q : i.mUpperPolys)
      {
        if (p == q) continue;
        Trace("cdcac") << "Resultant of " << p << " and " << q << " -> "
                       << resultant(p, q) << std::endl;
        add_polynomial(res, resultant(p, q));
      }
    }
  }

  for (std::size_t i = 0; i < intervals.size() - 1; ++i)
  {
    // Add resultants of consecutive intervals.
    cad::make_finest_square_free_basis(intervals[i].mUpperPolys,
                                       intervals[i + 1].mLowerPolys);
    for (const auto& p : intervals[i].mUpperPolys)
    {
      for (const auto& q : intervals[i + 1].mLowerPolys)
      {
        Trace("cdcac") << "Resultant of " << p << " and " << q << " -> "
                       << resultant(p, q) << std::endl;
        add_polynomial(res, resultant(p, q));
      }
    }
  }

  remove_duplicates(res);
  make_finest_square_free_basis(res);

  return res;
}

CACInterval CDCAC::interval_from_characterization(
    const std::vector<Polynomial>& characterization,
    std::size_t cur_variable,
    const Value& sample)
{
  std::vector<Polynomial> l;
  std::vector<Polynomial> u;
  std::vector<Polynomial> m;
  std::vector<Polynomial> d;

  for (const auto& p : characterization)
  {
    // Add polynomials to either main or down
    if (main_variable(p) == mVariableOrdering[cur_variable])
    {
      m.emplace_back(p);
    }
    else
    {
      d.emplace_back(p);
    }
  }

  // Collect -oo, all roots, oo
  std::vector<Value> roots;
  roots.emplace_back(Value::minus_infty());
  for (const auto& p : m)
  {
    auto tmp = isolate_real_roots(p, mAssignment);
    roots.insert(roots.end(), tmp.begin(), tmp.end());
  }
  roots.emplace_back(Value::plus_infty());
  std::sort(roots.begin(), roots.end());

  // Now find the interval bounds
  Value lower;
  Value upper;
  for (std::size_t i = 0; i < roots.size(); ++i)
  {
    if (sample < roots[i])
    {
      lower = roots[i - 1];
      upper = roots[i];
      break;
    }
    if (roots[i] == sample)
    {
      lower = sample;
      upper = sample;
      break;
    }
  }
  Assert(!is_none(lower) && !is_none(upper));

  if (lower != Value::minus_infty())
  {
    // Identify polynomials that have a root at the lower bound
    mAssignment.set(mVariableOrdering[cur_variable], lower);
    for (const auto& p : m)
    {
      if (evaluate_constraint(p, mAssignment, SignCondition::EQ))
      {
        l.emplace_back(p);
      }
    }
    mAssignment.unset(mVariableOrdering[cur_variable]);
  }
  if (upper != Value::plus_infty())
  {
    // Identify polynomials that have a root at the upper bound
    mAssignment.set(mVariableOrdering[cur_variable], upper);
    for (const auto& p : m)
    {
      if (evaluate_constraint(p, mAssignment, SignCondition::EQ))
      {
        u.emplace_back(p);
      }
    }
    mAssignment.unset(mVariableOrdering[cur_variable]);
  }

  if (lower == upper)
  {
    // construct a point interval
    return CACInterval{Interval(lower, false, upper, false), l, u, m, d, {}};
  }
  else
  {
    // construct an open interval
    Assert(lower < upper);
    return CACInterval{Interval(lower, true, upper, true), l, u, m, d, {}};
  }
}

std::vector<CACInterval> CDCAC::get_unsat_cover(std::size_t cur_variable,
                                                bool return_first_interval)
{
  return {};
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
