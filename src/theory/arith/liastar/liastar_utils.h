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

#ifdef CVC5_USE_NORMALIZ

#include "expr/node.h"
#include "smt/env.h"
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
  /**
   * @param a node in LIA that only contains =, >=, ite in its tree
   * @return a node in DNF where ite and = are eliminated
   */
  static Node toDNF(Node n, Env* e);

 private:
  static std::pair<Node, bool> booleanDNF(Node n, Env* e);
  static std::vector<std::pair<Node, Node>> integerDNF(Node n, Env* e);
};
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__LIASTAR__UTILS_H */

#endif /* CVC5_USE_NORMALIZ */