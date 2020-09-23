/*********************                                                        */
/*! \file variable_bounds.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **/

#include "theory/arith/nl/icp/variable_bounds.h"

#ifdef CVC4_POLY_IMP

#include "theory/arith/normal_form.h"
#include "util/poly_util.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

void VariableBounds::update_lower_bound(const Node& origin,
                                        const Node& variable,
                                        const poly::Value& value,
                                        bool strict)
{
  // variable > or >= value because of origin
  Trace("nl-icp") << "\tNew bound " << variable << (strict ? ">" : ">=")
                  << value << " due to " << origin << std::endl;
  Interval& i = get(variable);
  if (poly::is_none(i.lower) || i.lower < value)
  {
    i.lower = value;
    i.lower_strict = strict;
    i.lower_origin = origin;
  }
  else if (strict && i.lower == value)
  {
    i.lower_strict = strict;
    i.lower_origin = origin;
  }
}
void VariableBounds::update_upper_bound(const Node& origin,
                                        const Node& variable,
                                        const poly::Value& value,
                                        bool strict)
{
  // variable < or <= value because of origin
  Trace("nl-icp") << "\tNew bound " << variable << (strict ? "<" : "<=")
                  << value << " due to " << origin << std::endl;
  Interval& i = get(variable);
  if (poly::is_none(i.upper) || i.upper > value)
  {
    i.upper = value;
    i.upper_strict = strict;
    i.upper_origin = origin;
  }
  else if (strict && i.upper == value)
  {
    i.upper_strict = strict;
    i.upper_origin = origin;
  }
}

void VariableBounds::reset() { d_intervals.clear(); }

Interval& VariableBounds::get(const Node& v)
{
  auto it = d_intervals.find(v);
  if (it == d_intervals.end())
  {
    it = d_intervals.emplace(v, Interval()).first;
  }
  return it->second;
}
Interval VariableBounds::get(const Node& v) const
{
  auto it = d_intervals.find(v);
  if (it == d_intervals.end())
  {
    return Interval{};
  }
  return it->second;
}

poly::IntervalAssignment VariableBounds::get() const
{
  poly::IntervalAssignment res;
  for (const auto& vi : d_intervals)
  {
    poly::Variable v = d_mapper(vi.first);
    poly::Interval i(vi.second.lower,
                     vi.second.lower_strict,
                     vi.second.upper,
                     vi.second.upper_strict);
    res.set(v, i);
  }
  return res;
}
bool VariableBounds::add(const Node& n)
{
  // Parse the node as a comparison
  auto comp = Comparison::parseNormalForm(n);
  auto dec = comp.decompose(true);
  if (std::get<0>(dec).isVariable())
  {
    Variable v = std::get<0>(dec).getVariable();
    Kind relation = std::get<1>(dec);
    if (relation == Kind::DISTINCT) return false;
    Constant bound = std::get<2>(dec);
    // has the form  v  ~relation~  bound

    poly::Value val = node_to_value(bound.getNode(), v.getNode());
    poly::Interval newi = poly::Interval::full();

    Maybe<Node> res;
    switch (relation)
    {
      case Kind::LEQ: update_upper_bound(n, v.getNode(), val, false); break;
      case Kind::LT: update_upper_bound(n, v.getNode(), val, true); break;
      case Kind::EQUAL:
        update_lower_bound(n, v.getNode(), val, false);
        update_upper_bound(n, v.getNode(), val, false);
        break;
      case Kind::GT: update_lower_bound(n, v.getNode(), val, true); break;
      case Kind::GEQ: update_lower_bound(n, v.getNode(), val, false); break;
      default: Assert(false);
    }
    d_mapper(v.getNode());
    return true;
  }
  return false;
}

std::ostream& operator<<(std::ostream& os, const VariableBounds& vb)
{
  os << "Bounds:" << std::endl;
  for (const auto& var : vb.getMapper().mVarCVCpoly)
  {
    os << "\t" << var.first << " -> " << vb.get(var.first) << std::endl;
    ;
  }
  return os;
}

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
