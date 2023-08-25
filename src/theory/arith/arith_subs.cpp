/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic substitution utility.
 */

#include "theory/arith/arith_subs.h"

#include "theory/arith/arith_utilities.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

void ArithSubs::addArith(const Node& v, const Node& s)
{
  Assert(v.getType().isRealOrInt());
  Assert(s.getType().isRealOrInt());
  d_vars.push_back(v);
  d_subs.push_back(s);
}

Node ArithSubs::applyArith(const Node& n) const
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::vector<TNode> visit;
  visit.push_back(n);
  do
  {
    TNode cur = visit.back();
    visit.pop_back();
    auto it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      Kind ck = cur.getKind();
      auto s = find(cur);
      if (s)
      {
        visited[cur] = *s;
      }
      else if (cur.getNumChildren() == 0)
      {
        visited[cur] = cur;
      }
      else
      {
        TheoryId ctid = theory::kindToTheoryId(ck);
        if ((ctid != THEORY_ARITH && ctid != THEORY_BOOL
             && ctid != THEORY_BUILTIN)
            || isTranscendentalKind(ck))
        {
          // Do not traverse beneath applications that belong to another theory
          // besides (core) arithmetic. Notice that transcendental function
          // applications are also not traversed here.
          visited[cur] = cur;
        }
        else
        {
          visit.push_back(cur);
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
