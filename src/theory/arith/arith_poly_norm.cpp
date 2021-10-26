/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utility for polynomial normalization
 */

#include "theory/arith/arith_poly_norm.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {

bool isArithPolyNorm(Node n, Node p)
{
  Node nn = arithPolyNorm(n);
  
  return false;
}

Node arithPolyNorm(Node n)
{
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    it = visited.find(cur);
    Kind k = cur.getKind();
    if (it == visited.end()) {
      if (k==PLUS || k==MINUS || k==UMINUS || k==MULT || k==NONLINEAR_MULT)
      {
        // it is a leaf
        visited[cur] = cur;
        visit.pop_back();
      }
      else
      {
        visited[cur] = Node::null();
        for (const Node& cn : cur) {
          visit.push_back(cn);
        }
      }
      continue;
    }
    visit.pop_back();
    if (it->second.isNull()) 
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      Assert (cur.getMetaKind() != kind::metakind::PARAMETERIZED);
      for (const Node& cn : cur) {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      switch (k)
      {
        case PLUS:
          break;
        case MINUS:
          break;
        case UMINUS:
          break;
        case MULT:
          break;
        case NONLINEAR_MULT:
          break;
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
}  // namespace cvc5
