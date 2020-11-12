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
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {

std::ostream& operator<<(std::ostream& os, const Bounds& b) {
  return os << (b.lower_strict ? '(' : '[') << b.lower_value << " .. "
            << b.upper_value << (b.upper_strict ? ')' : ']');
}

void BoundInference::reset() { d_bounds.clear(); }

Bounds& BoundInference::get_or_add(const Node& lhs)
{
  auto it = d_bounds.find(lhs);
  if (it == d_bounds.end())
  {
    it = d_bounds.emplace(lhs, Bounds()).first;
  }
  return it->second;
}
Bounds BoundInference::get(const Node& lhs) const
{
  auto it = d_bounds.find(lhs);
  if (it == d_bounds.end())
  {
    return Bounds{};
  }
  return it->second;
}

const std::map<Node, Bounds>& BoundInference::get() const { return d_bounds; }
bool BoundInference::add(const Node& n, bool onlyVariables)
{
  Node tmp = Rewriter::rewrite(n);
  if (tmp.getKind() == Kind::CONST_BOOLEAN)
  {
    return false;
  }
  // Parse the node as a comparison
  auto comp = Comparison::parseNormalForm(tmp);
  auto dec = comp.decompose(true);
  if (onlyVariables && !std::get<0>(dec).isVariable())
  {
    return false;
  }

  Node lhs = std::get<0>(dec).getNode();
  Kind relation = std::get<1>(dec);
  if (relation == Kind::DISTINCT) return false;
  Node bound = std::get<2>(dec).getNode();
  // has the form  lhs  ~relation~  bound

  if (lhs.getType().isInteger())
  {
    Rational br = bound.getConst<Rational>();
    auto* nm = NodeManager::currentNM();
    switch (relation)
    {
      case Kind::LEQ: bound = nm->mkConst<Rational>(br.floor()); break;
      case Kind::LT:
        bound = nm->mkConst<Rational>((br - 1).ceiling());
        relation = Kind::LEQ;
        break;
      case Kind::GT:
        bound = nm->mkConst<Rational>((br + 1).floor());
        relation = Kind::GEQ;
        break;
      case Kind::GEQ: bound = nm->mkConst<Rational>(br.ceiling()); break;
      default:;
    }
    Trace("bound-inf") << "Strengthened " << n << " to " << lhs << " "
                       << relation << " " << bound << std::endl;
  }

  switch (relation)
  {
    case Kind::LEQ: update_upper_bound(n, lhs, bound, false); break;
    case Kind::LT: update_upper_bound(n, lhs, bound, true); break;
    case Kind::EQUAL:
      update_lower_bound(n, lhs, bound, false);
      update_upper_bound(n, lhs, bound, false);
      break;
    case Kind::GT: update_lower_bound(n, lhs, bound, true); break;
    case Kind::GEQ: update_lower_bound(n, lhs, bound, false); break;
    default: Assert(false);
  }
  return true;
}

void BoundInference::replaceByOrigins(std::vector<Node>& nodes) const
{
  std::vector<Node> toAdd;
  for (auto& n : nodes)
  {
    for (const auto& b : d_bounds)
    {
      if (n == b.second.lower_bound && n == b.second.upper_bound)
      {
        if (n != b.second.lower_origin && n != b.second.upper_origin)
        {
          Trace("bound-inf")
              << "Replace " << n << " by origins " << b.second.lower_origin
              << " and " << b.second.upper_origin << std::endl;
          n = b.second.lower_origin;
          toAdd.emplace_back(b.second.upper_origin);
        }
      }
      else if (n == b.second.lower_bound)
      {
        if (n != b.second.lower_origin)
        {
          Trace("bound-inf") << "Replace " << n << " by origin "
                             << b.second.lower_origin << std::endl;
          n = b.second.lower_origin;
        }
      }
      else if (n == b.second.upper_bound)
      {
        if (n != b.second.upper_origin)
        {
          Trace("bound-inf") << "Replace " << n << " by origin "
                             << b.second.upper_origin << std::endl;
          n = b.second.upper_origin;
        }
      }
    }
  }
  nodes.insert(nodes.end(), toAdd.begin(), toAdd.end());
}

void BoundInference::update_lower_bound(const Node& origin,
                                        const Node& lhs,
                                        const Node& value,
                                        bool strict)
{
  // lhs > or >= value because of origin
  Trace("bound-inf") << "\tNew bound " << lhs << (strict ? ">" : ">=") << value
                     << " due to " << origin << std::endl;
  Bounds& b = get_or_add(lhs);
  if (b.lower_value.isNull()
      || b.lower_value.getConst<Rational>() < value.getConst<Rational>())
  {
    auto* nm = NodeManager::currentNM();
    b.lower_value = value;
    b.lower_strict = strict;

    b.lower_origin = origin;

    if (!b.lower_strict && !b.upper_strict && b.lower_value == b.upper_value)
    {
      b.lower_bound = b.upper_bound =
          Rewriter::rewrite(nm->mkNode(Kind::EQUAL, lhs, value));
    }
    else
    {
      b.lower_bound = Rewriter::rewrite(
          nm->mkNode(strict ? Kind::GT : Kind::GEQ, lhs, value));
    }
  }
  else if (strict && b.lower_value == value)
  {
    auto* nm = NodeManager::currentNM();
    b.lower_strict = strict;
    b.lower_bound = Rewriter::rewrite(nm->mkNode(Kind::GT, lhs, value));
    b.lower_origin = origin;
  }
}
void BoundInference::update_upper_bound(const Node& origin,
                                        const Node& lhs,
                                        const Node& value,
                                        bool strict)
{
  // lhs < or <= value because of origin
  Trace("bound-inf") << "\tNew bound " << lhs << (strict ? "<" : "<=") << value
                     << " due to " << origin << std::endl;
  Bounds& b = get_or_add(lhs);
  if (b.upper_value.isNull()
      || b.upper_value.getConst<Rational>() > value.getConst<Rational>())
  {
    auto* nm = NodeManager::currentNM();
    b.upper_value = value;
    b.upper_strict = strict;
    b.upper_origin = origin;
    if (!b.lower_strict && !b.upper_strict && b.lower_value == b.upper_value)
    {
      b.lower_bound = b.upper_bound =
          Rewriter::rewrite(nm->mkNode(Kind::EQUAL, lhs, value));
    }
    else
    {
      b.upper_bound = Rewriter::rewrite(
          nm->mkNode(strict ? Kind::LT : Kind::LEQ, lhs, value));
    }
  }
  else if (strict && b.upper_value == value)
  {
    auto* nm = NodeManager::currentNM();
    b.upper_strict = strict;
    b.upper_bound = Rewriter::rewrite(nm->mkNode(Kind::LT, lhs, value));
    b.upper_origin = origin;
  }
}

std::ostream& operator<<(std::ostream& os, const BoundInference& bi)
{
  os << "Bounds:" << std::endl;
  for (const auto& b : bi.get())
  {
    os << "\t" << b.first << " -> " << b.second.lower_value << ".."
       << b.second.upper_value << std::endl;
  }
  return os;
}

std::map<Node, std::pair<Node,Node>> getBounds(const std::vector<Node>& assertions) {
  BoundInference bi;
  for (const auto& a: assertions) {
    bi.add(a);
  }
  std::map<Node, std::pair<Node,Node>> res;
  for (const auto& b : bi.get())
  {
    res.emplace(b.first,
                std::make_pair(b.second.lower_value, b.second.upper_value));
  }
  return res;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
