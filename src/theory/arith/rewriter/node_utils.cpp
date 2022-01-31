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
 * Utilities for nodes in the arithmetic rewriter.
 */

#include "theory/arith/rewriter/node_utils.h"

#include "base/check.h"

namespace cvc5::theory::arith::rewriter {

bool isIntegral(TNode n)
{
  std::vector<TNode> queue = {n};
  while (!queue.empty())
  {
    TNode cur = queue.back();
    queue.pop_back();

    if (cur.isConst()) continue;
    switch (cur.getKind())
    {
      case Kind::LT:
      case Kind::LEQ:
      case Kind::EQUAL:
      case Kind::DISTINCT:
      case Kind::GEQ:
      case Kind::GT:
        queue.emplace_back(n[0]);
        queue.emplace_back(n[1]);
        break;
      case Kind::PLUS:
      case Kind::MULT:
      case Kind::MINUS:
      case Kind::UMINUS:
        queue.insert(queue.end(), cur.begin(), cur.end());
        break;
      default:
        if (!cur.getType().isInteger()) return false;
    }
  }
  return true;
}

}
