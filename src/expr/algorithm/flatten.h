/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for flattening nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__ALGORITHMS__FLATTEN_H
#define CVC5__EXPR__ALGORITHMS__FLATTEN_H

#include <algorithm>

#include "expr/node.h"

namespace cvc5::internal::expr::algorithm {

/**
 * Flatten a node into a vector of its (direct or indirect) children.
 * Optionally, a sequence of kinds that should be flattened can be passed. If no
 * kinds are given, flattening is done based on the kind of t.
 * Note that flatten(t, c) is equivalent to flatten(t, c, t.getKind()).
 * @param t The node to be flattened
 * @param children The resulting list of children
 * @param kinds Optional sequence of kinds to consider for flattening
 */
template <typename... Kinds>
void flatten(TNode t, std::vector<TNode>& children, Kinds... kinds)
{
  std::vector<TNode> queue = {t};
  while (!queue.empty())
  {
    TNode cur = queue.back();
    queue.pop_back();
    bool recurse = false;
    // figure out whether to recurse into cur
    if constexpr (sizeof...(kinds) == 0)
    {
      recurse = t.getKind() == cur.getKind();
    }
    else
    {
      recurse = ((kinds == cur.getKind()) || ...);
    }
    if (recurse)
    {
      queue.insert(queue.end(), cur.rbegin(), cur.rend());
    }
    else
    {
      children.emplace_back(cur);
    }
  }
}

/**
 * Check whether a node can be flattened, that is whether calling flatten()
 * returns something other than its direct children. If no kinds are passed
 * explicitly, this simply checks whether any of the children has the same kind
 * as t. If a sequence of kinds is passed, this checks whether any of the
 * children has one of these kinds.
 * Note that canFlatten(t) is equivalent to canFlatten(t, t.getKind()).
 * @param t The node that should be checked
 * @param kinds Optional sequence of kinds
 * @return true iff t could be flattened
 */
template <typename... Kinds>
bool canFlatten(TNode t, Kinds... kinds)
{
  if constexpr (sizeof...(kinds) == 0)
  {
    return std::any_of(t.begin(), t.end(), [k = t.getKind()](TNode child) {
      return child.getKind() == k;
    });
  }
  else
  {
    if (!((t.getKind() == kinds) || ...))
    {
      return false;
    }
    return std::any_of(t.begin(), t.end(), [=](TNode child) {
      return ((child.getKind() == kinds) || ...);
    });
  }
}

/**
 * If t can be flattened, return a new node of the same kind as t with the
 * flattened children. Otherwise, return t.
 * If a sequence of kinds is given, the flattening (and the respective check)
 * are done with respect to these kinds: see the documentation of flatten()
 * and canFlatten() for more details.
 * @param t The node to be flattened
 * @param kinds Optional sequence of kinds
 * @return A flattened version of t
 */
template <typename... Kinds>
Node flatten(TNode t, Kinds... kinds)
{
  if (!canFlatten(t, kinds...))
  {
    return t;
  }
  std::vector<TNode> children;
  flatten(t, children, kinds...);
  return NodeManager::currentNM()->mkNode(t.getKind(), children);
}

}  // namespace cvc5::internal::expr

#endif
