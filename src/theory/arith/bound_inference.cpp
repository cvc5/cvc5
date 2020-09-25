/*********************                                                        */
/*! \file bound_inference.cpp
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

#include "theory/arith/bound_inference.h"

#include "theory/arith/normal_form.h"

namespace CVC4 {
namespace theory {
namespace arith {

std::ostream& operator<<(std::ostream& os, const Bounds& b) {

  return os << (b.lower_strict ? '(' : '[') << b.lower << " .. " << b.upper
            << (b.upper_strict ? ')' : ']');

}

void BoundInference::update_lower_bound(const Node& origin,
                                        const Node& variable,
                                        const Node& value,
                                        bool strict)
{
  // variable > or >= value because of origin
  Trace("nl-icp") << "\tNew bound " << variable << (strict ? ">" : ">=")
                  << value << " due to " << origin << std::endl;
  Bounds& b = get_or_add(variable);
  if (b.lower.isNull() || b.lower.getConst<Rational>() < value.getConst<Rational>())
  {
    b.lower = value;
    b.lower_strict = strict;
    b.lower_origin = origin;
  }
  else if (strict && b.lower == value)
  {
    b.lower_strict = strict;
    b.lower_origin = origin;
  }
}
void BoundInference::update_upper_bound(const Node& origin,
                                        const Node& variable,
                                        const Node& value,
                                        bool strict)
{
  // variable < or <= value because of origin
  Trace("nl-icp") << "\tNew bound " << variable << (strict ? "<" : "<=")
                  << value << " due to " << origin << std::endl;
  Bounds& b = get_or_add(variable);
  if (b.upper.isNull() || b.upper.getConst<Rational>() > value.getConst<Rational>())
  {
    b.upper = value;
    b.upper_strict = strict;
    b.upper_origin = origin;
  }
  else if (strict && b.upper == value)
  {
    b.upper_strict = strict;
    b.upper_origin = origin;
  }
}

void BoundInference::reset() { d_bounds.clear(); }

Bounds& BoundInference::get_or_add(const Node& v)
{
  auto it = d_bounds.find(v);
  if (it == d_bounds.end())
  {
    it = d_bounds.emplace(v, Bounds()).first;
  }
  return it->second;
}
Bounds BoundInference::get(const Node& v) const
{
  auto it = d_bounds.find(v);
  if (it == d_bounds.end())
  {
    return Bounds{};
  }
  return it->second;
}

const std::map<Node, Bounds>& BoundInference::get() const { return d_bounds; }
bool BoundInference::add(const Node& n)
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

    switch (relation)
    {
      case Kind::LEQ:
        update_upper_bound(n, v.getNode(), bound.getNode(), false);
        break;
      case Kind::LT:
        update_upper_bound(n, v.getNode(), bound.getNode(), true);
        break;
      case Kind::EQUAL:
        update_lower_bound(n, v.getNode(), bound.getNode(), false);
        update_upper_bound(n, v.getNode(), bound.getNode(), false);
        break;
      case Kind::GT:
        update_lower_bound(n, v.getNode(), bound.getNode(), true);
        break;
      case Kind::GEQ:
        update_lower_bound(n, v.getNode(), bound.getNode(), false);
        break;
      default: Assert(false);
    }
    return true;
  }
  return false;
}

std::ostream& operator<<(std::ostream& os, const BoundInference& bi)
{
  os << "Bounds:" << std::endl;
  for (const auto& vb : bi.get())
  {
    os << "\t" << vb.first << " -> " << vb.second.lower << ".."
       << vb.second.upper << std::endl;
  }
  return os;
}

std::map<Node, std::pair<Node,Node>> getBounds(const std::vector<Node>& assertions) {
  BoundInference bi;
  for (const auto& a: assertions) {
    bi.add(a);
  }
  std::map<Node, std::pair<Node,Node>> res;
  for (const auto& vb: bi.get()) {
    res.emplace(vb.first, std::make_pair(vb.second.lower, vb.second.upper));
  }
  return res;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
