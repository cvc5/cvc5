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
 * Implements utilities for cdcac.
 */

#include "theory/arith/nl/cad/cdcac_utils.h"

#ifdef CVC5_POLY_IMP

#include "theory/arith/nl/cad/projections.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

using namespace poly;

bool operator==(const CACInterval& lhs, const CACInterval& rhs)
{
  return lhs.d_interval == rhs.d_interval;
}
bool operator<(const CACInterval& lhs, const CACInterval& rhs)
{
  return lhs.d_interval < rhs.d_interval;
}

/**
 * Induces an ordering on poly intervals that is suitable for redundancy
 * removal as implemented in clean_intervals.
 */
inline bool compareForCleanup(const Interval& lhs, const Interval& rhs)
{
  const lp_value_t* ll = &(lhs.get_internal()->a);
  const lp_value_t* lu =
      lhs.get_internal()->is_point ? ll : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  const lp_value_t* ru =
      rhs.get_internal()->is_point ? rl : &(rhs.get_internal()->b);

  int lc = lp_value_cmp(ll, rl);
  // Lower bound is smaller
  if (lc < 0) return true;
  // Lower bound is larger
  if (lc > 0) return false;
  // Lower bound type is smaller
  if (!lhs.get_internal()->a_open && rhs.get_internal()->a_open) return true;
  // Lower bound type is larger
  if (lhs.get_internal()->a_open && !rhs.get_internal()->a_open) return false;

  // Attention: Here it differs from the regular interval ordering!
  int uc = lp_value_cmp(lu, ru);
  // Upper bound is smaller
  if (uc < 0) return false;
  // Upper bound is larger
  if (uc > 0) return true;
  // Upper bound type is smaller
  if (lhs.get_internal()->b_open && !rhs.get_internal()->b_open) return false;
  // Upper bound type is larger
  if (!lhs.get_internal()->b_open && rhs.get_internal()->b_open) return true;

  // Identical
  return false;
}

bool intervalCovers(const Interval& lhs, const Interval& rhs)
{
  const lp_value_t* ll = &(lhs.get_internal()->a);
  const lp_value_t* lu =
      lhs.get_internal()->is_point ? ll : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  const lp_value_t* ru =
      rhs.get_internal()->is_point ? rl : &(rhs.get_internal()->b);

  int lc = lp_value_cmp(ll, rl);
  int uc = lp_value_cmp(lu, ru);

  // Lower bound is smaller and upper bound is larger
  if (lc < 0 && uc > 0) return true;
  // Lower bound is larger or upper bound is smaller
  if (lc > 0 || uc < 0) return false;

  // Now both bounds are identical.
  Assert(lc <= 0 && uc >= 0);
  Assert(lc == 0 || uc == 0);

  // Lower bound is the same and the bound type is stricter
  if (lc == 0 && lhs.get_internal()->a_open && !rhs.get_internal()->a_open)
    return false;
  // Upper bound is the same and the bound type is stricter
  if (uc == 0 && lhs.get_internal()->b_open && !rhs.get_internal()->b_open)
    return false;

  // Both bounds are weaker
  return true;
}

bool intervalConnect(const Interval& lhs, const Interval& rhs)
{
  Assert(lhs < rhs) << "Can only check for a connection if lhs < rhs.";
  const lp_value_t* lu = lhs.get_internal()->is_point
                             ? &(lhs.get_internal()->a)
                             : &(lhs.get_internal()->b);
  const lp_value_t* rl = &(rhs.get_internal()->a);
  int c = lp_value_cmp(lu, rl);
  if (c < 0)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs << " are separated." << std::endl;
    return false;
  }
  if (c > 0)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs << " overlap." << std::endl;
    return true;
  }
  Assert(c == 0);
  if (lhs.get_internal()->is_point || rhs.get_internal()->is_point
      || !lhs.get_internal()->b_open || !rhs.get_internal()->a_open)
  {
    Trace("libpoly::interval_connect")
        << lhs << " and " << rhs
        << " touch and the intermediate point is covered." << std::endl;
    return true;
  }
  return false;
}

void cleanIntervals(std::vector<CACInterval>& intervals)
{
  // Simplifies removal of redundancies later on.
  if (intervals.size() < 2) return;

  // Sort intervals.
  std::sort(intervals.begin(),
            intervals.end(),
            [](const CACInterval& lhs, const CACInterval& rhs) {
              return compareForCleanup(lhs.d_interval, rhs.d_interval);
            });

  // Remove intervals that are covered by others.
  // Implementation roughly follows
  // https://en.cppreference.com/w/cpp/algorithm/remove Find first interval that
  // covers the next one.
  std::size_t first = 0;
  for (std::size_t n = intervals.size(); first < n - 1; ++first)
  {
    if (intervalCovers(intervals[first].d_interval,
                       intervals[first + 1].d_interval))
    {
      break;
    }
  }
  // If such an interval exists, remove accordingly.
  if (first < intervals.size() - 1)
  {
    for (std::size_t i = first + 2, n = intervals.size(); i < n; ++i)
    {
      if (!intervalCovers(intervals[first].d_interval, intervals[i].d_interval))
      {
        // Interval is not covered. Move it to the front and bump front.
        ++first;
        intervals[first] = std::move(intervals[i]);
      }
      // Else: Interval is covered as well.
    }
    // Erase trailing values
    while (intervals.size() > first + 1)
    {
      intervals.pop_back();
    }
  }
}

std::vector<Node> collectConstraints(const std::vector<CACInterval>& intervals)
{
  std::vector<Node> res;
  for (const auto& i : intervals)
  {
    res.insert(res.end(), i.d_origins.begin(), i.d_origins.end());
  }
  std::sort(res.begin(), res.end());
  auto it = std::unique(res.begin(), res.end());
  res.erase(it, res.end());
  return res;
}

bool sampleOutside(const std::vector<CACInterval>& infeasible, Value& sample)
{
  if (infeasible.empty())
  {
    // No infeasible region, just take anything: zero
    sample = poly::Integer();
    return true;
  }
  if (!is_minus_infinity(get_lower(infeasible.front().d_interval)))
  {
    // First does not cover -oo, just take sufficiently low value
    Trace("cdcac") << "Sample before " << infeasible.front().d_interval
                   << std::endl;
    const auto* i = infeasible.front().d_interval.get_internal();
    sample = value_between(
        Value::minus_infty().get_internal(), true, &i->a, !i->a_open);
    return true;
  }
  for (std::size_t i = 0, n = infeasible.size(); i < n - 1; ++i)
  {
    // Search for two subsequent intervals that do not connect
    if (!intervalConnect(infeasible[i].d_interval,
                         infeasible[i + 1].d_interval))
    {
      // Two intervals do not connect, take something from the gap
      const auto* l = infeasible[i].d_interval.get_internal();
      const auto* r = infeasible[i + 1].d_interval.get_internal();

      Trace("cdcac") << "Sample between " << infeasible[i].d_interval << " and "
                     << infeasible[i + 1].d_interval << std::endl;

      if (l->is_point)
      {
        sample = value_between(&l->a, true, &r->a, !r->a_open);
      }
      else
      {
        sample = value_between(&l->b, !l->b_open, &r->a, !r->a_open);
      }
      return true;
    }
    else
    {
      Trace("cdcac") << infeasible[i].d_interval << " and "
                     << infeasible[i + 1].d_interval << " connect" << std::endl;
    }
  }
  if (!is_plus_infinity(get_upper(infeasible.back().d_interval)))
  {
    // Last does not cover oo, just take something sufficiently large
    Trace("cdcac") << "Sample above " << infeasible.back().d_interval
                   << std::endl;
    const auto* i = infeasible.back().d_interval.get_internal();
    if (i->is_point)
    {
      sample =
          value_between(&i->a, true, Value::plus_infty().get_internal(), true);
    }
    else
    {
      sample = value_between(
          &i->b, !i->b_open, Value::plus_infty().get_internal(), true);
    }
    return true;
  }
  return false;
}

namespace {
/**
 * Replace a polynomial at polys[id] with the given pair of polynomials.
 * Also update d_mainPolys in the given interval accordingly.
 * If one of the factors (from the pair) is from a lower level (has a different
 * main variable), push this factor to the d_downPolys.
 * The first factor needs to be a proper polynomial (!is_constant(subst.first)),
 * but the second factor may be anything.
 */
void replace_polynomial(PolyVector& polys,
                        std::size_t id,
                        std::pair<poly::Polynomial, poly::Polynomial> subst,
                        CACInterval& interval)
{
  Assert(polys[id] == subst.first * subst.second);
  Assert(!is_constant(subst.first));
  // Whether polys[id] has already been replaced
  bool replaced = false;
  poly::Variable var = main_variable(polys[id]);
  // The position within interval.d_mainPolys to be replaced.
  auto mit = std::find(
      interval.d_mainPolys.begin(), interval.d_mainPolys.end(), polys[id]);
  if (main_variable(subst.first) == var)
  {
    // Replace in polys[id] and *mit
    polys[id] = subst.first;
    if (mit != interval.d_mainPolys.end())
    {
      *mit = subst.first;
    }
    replaced = true;
  }
  else
  {
    // Push to d_downPolys
    interval.d_downPolys.add(subst.first);
  }
  // Skip constant poly
  if (!is_constant(subst.second))
  {
    if (main_variable(subst.second) == var)
    {
      if (replaced)
      {
        // Append to polys and d_mainPolys
        polys.add(subst.second);
        interval.d_mainPolys.add(subst.second);
      }
      else
      {
        // Replace in polys[id] and *mit
        polys[id] = subst.second;
        if (mit != interval.d_mainPolys.end())
        {
          *mit = subst.second;
        }
        replaced = true;
      }
    }
    else
    {
      // Push to d_downPolys
      interval.d_downPolys.add(subst.second);
    }
  }
  Assert(replaced)
      << "At least one of the factors should have the main variable";
}
}  // namespace

void makeFinestSquareFreeBasis(CACInterval& lhs, CACInterval& rhs)
{
  auto& l = lhs.d_upperPolys;
  auto& r = rhs.d_lowerPolys;
  if (l.empty()) return;
  for (std::size_t i = 0, ln = l.size(); i < ln; ++i)
  {
    for (std::size_t j = 0, rn = r.size(); j < rn; ++j)
    {
      // All main variables should be the same
      Assert(main_variable(l[i]) == main_variable(r[j]));
      if (l[i] == r[j]) continue;
      Polynomial g = gcd(l[i], r[j]);
      if (!is_constant(g))
      {
        auto newl = div(l[i], g);
        auto newr = div(r[j], g);
        replace_polynomial(l, i, std::make_pair(g, newl), lhs);
        replace_polynomial(r, j, std::make_pair(g, newr), rhs);
      }
    }
  }
  l.reduce();
  r.reduce();
  lhs.d_mainPolys.reduce();
  rhs.d_mainPolys.reduce();
  lhs.d_downPolys.reduce();
  rhs.d_downPolys.reduce();
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
