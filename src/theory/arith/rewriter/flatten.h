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
 * Flattening utilities for the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__FLATTEN_H
#define CVC5__THEORY__ARITH__REWRITER__FLATTEN_H

#include <algorithm>

#include "base/check.h"
#include "expr/node.h"

namespace cvc5::theory::arith::rewriter {


/** Flatten the given node (with child nodes of the same kind) into a vector */
void flatten(TNode t, std::vector<TNode>& children)
{
  Kind k = t.getKind();
  for (const auto& child : t)
  {
    if (child.getKind() == k)
    {
      flatten(child, children);
    }
    else
    {
      children.emplace_back(child);
    }
  }
}

/** Flatten the given node (with child nodes of the same kind) */
Node flatten(TNode t)
{
  Kind k = t.getKind();
  bool canFlatten = std::any_of(
      t.begin(), t.end(), [k](TNode child) { return child.getKind() == k; });
  if (!canFlatten)
  {
    return t;
  }
  std::vector<TNode> children;
  flatten(t, children);
  Assert(children.size() >= 2);
  return NodeManager::currentNM()->mkNode(t.getKind(), std::move(children));
}

/**
 * Flatten the given node (with child nodes of one of the given kinds) into a
 * vector.
 */
void flattenMultiplication(TNode t,
                              std::vector<TNode>& children)
{
  Assert(t.getKind() == Kind::MULT || t.getKind() == Kind::NONLINEAR_MULT);
  for (const auto& child : t)
  {
    if (child.getKind() == Kind::MULT || child.getKind() == Kind::NONLINEAR_MULT)
    {
      flattenMultiplication(child, children);
    }
    else
    {
      children.emplace_back(child);
    }
  }
}

}

#endif
