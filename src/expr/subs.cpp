/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple substitution utility.
 */

#include "expr/subs.h"

#include <sstream>

#include "expr/skolem_manager.h"

namespace cvc5::internal {

bool Subs::empty() const { return d_vars.empty(); }

size_t Subs::size() const { return d_vars.size(); }

bool Subs::contains(Node v) const
{
  return std::find(d_vars.begin(), d_vars.end(), v) != d_vars.end();
}

Node Subs::getSubs(Node v) const
{
  std::vector<Node>::const_iterator it =
      std::find(d_vars.begin(), d_vars.end(), v);
  if (it == d_vars.end())
  {
    return Node::null();
  }
  size_t i = std::distance(d_vars.begin(), it);
  Assert(i < d_subs.size());
  return d_subs[i];
}

std::optional<Node> Subs::find(TNode v) const
{
  auto it = std::find(d_vars.begin(), d_vars.end(), v);
  if (it == d_vars.end())
  {
    return {};
  }
  return d_subs[std::distance(d_vars.begin(), it)];
}

void Subs::add(Node v)
{
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  // default, use a fresh skolem of the same type
  Node s = sm->mkDummySkolem("sk", v.getType());
  add(v, s);
}

void Subs::add(const std::vector<Node>& vs)
{
  for (const Node& v : vs)
  {
    add(v);
  }
}

void Subs::add(const Node& v, const Node& s)
{
  Assert(s.isNull() || v.getType() == s.getType());
  d_vars.push_back(v);
  d_subs.push_back(s);
}

void Subs::add(const std::vector<Node>& vs, const std::vector<Node>& ss)
{
  Assert(vs.size() == ss.size());
  for (size_t i = 0, nvs = vs.size(); i < nvs; i++)
  {
    add(vs[i], ss[i]);
  }
}

void Subs::addEquality(Node eq)
{
  Assert(eq.getKind() == kind::EQUAL);
  add(eq[0], eq[1]);
}

void Subs::append(Subs& s)
{
  // add the substitution list
  add(s.d_vars, s.d_subs);
}

Node Subs::apply(const Node& n) const
{
  if (d_vars.empty())
  {
    return n;
  }
  Node ns =
      n.substitute(d_vars.begin(), d_vars.end(), d_subs.begin(), d_subs.end());
  return ns;
}
Node Subs::rapply(Node n) const
{
  if (d_vars.empty())
  {
    return n;
  }
  Node ns =
      n.substitute(d_subs.begin(), d_subs.end(), d_vars.begin(), d_vars.end());
  return ns;
}

void Subs::applyToRange(Subs& s) const
{
  if (d_vars.empty())
  {
    return;
  }
  for (size_t i = 0, ns = s.d_subs.size(); i < ns; i++)
  {
    s.d_subs[i] = apply(s.d_subs[i]);
  }
}

void Subs::rapplyToRange(Subs& s) const
{
  if (d_vars.empty())
  {
    return;
  }
  for (size_t i = 0, ns = s.d_subs.size(); i < ns; i++)
  {
    s.d_subs[i] = rapply(s.d_subs[i]);
  }
}

Node Subs::getEquality(size_t i) const
{
  Assert(i < d_vars.size());
  return d_vars[i].eqNode(d_subs[i]);
}

std::map<Node, Node> Subs::toMap() const
{
  std::map<Node, Node> ret;
  for (size_t i = 0, nvs = d_vars.size(); i < nvs; i++)
  {
    ret[d_vars[i]] = d_subs[i];
  }
  return ret;
}

std::string Subs::toString() const
{
  std::stringstream ss;
  ss << "[";
  for (size_t i = 0, nvs = d_vars.size(); i < nvs; i++)
  {
    if (i > 0)
    {
      ss << " ";
    }
    ss << d_vars[i] << " -> " << d_subs[i];
  }
  ss << "]";
  return ss.str();
}

void Subs::clear()
{
  d_vars.clear();
  d_subs.clear();
}

std::ostream& operator<<(std::ostream& out, const Subs& s)
{
  out << s.toString();
  return out;
}

}  // namespace cvc5::internal
