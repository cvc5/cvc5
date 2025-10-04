/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for liastar extension.
 */

#ifndef CVC5__THEORY__LIASTAR__UTILS_H
#define CVC5__THEORY__LIASTAR__UTILS_H

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

class LiaStarUtils
{
 public:
  /**
   * @param n a node of the form (int.star-contains (x1 ... xn) (p x1 ... xn)
   * (y1 ... yn))
   * @return <(p y1 ... yn), (and (>= y1 0) ... (>= yn 0))
   */
  static std::pair<Node, Node> getVectorPredicate(Node n, NodeManager* nm);
};
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__LIASTAR__UTILS_H */
