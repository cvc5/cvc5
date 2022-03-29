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
 * Utility functions for relations.
 */

#ifndef SRC_THEORY_SETS_RELS_UTILS_H_
#define SRC_THEORY_SETS_RELS_UTILS_H_

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace sets {

class RelsUtils
{
 public:
  /**
   * compute the transitive closure of a binary relation
   * @param members constant nodes of type (Tuple E E) that are known to in the
   * relation rel
   * @param rel a binary relation of type (Set (Tuple E E))
   * @pre all members need to be constants
   * @return the transitive closure of the relation
   */
  static std::set<Node> computeTC(const std::set<Node>& members, Node rel);

  /**
   * add all pairs (a, c) to the transitive closures where c is reachable from b
   * in the transitive relation in a depth first search manner.
   * @param rel a binary relation of type (Set (Tuple E E))
   * @param members constant nodes of type (Tuple E E) that are known to be in
   * the relation rel
   * @param a a node of type E where (a,b) is an element in the transitive
   * closure
   * @param b a node of type E where (a,b) is an element in the transitive
   * closure
   * @param traversed the set of members that have been visited so far
   * @param transitiveClosureMembers members of the transitive closure computed
   * so far
   */
  static void computeTC(Node rel,
                        const std::set<Node>& members,
                        Node a,
                        Node b,
                        std::set<Node>& traversed,
                        std::set<Node>& transitiveClosureMembers);

  /**
   * construct a pair from two elements
   * @param rel a node of type (Set (Tuple E E))
   * @param a a node of type E
   * @param b a node of type E
   * @return  a tuple (tuple a b)
   */
  static Node constructPair(Node rel, Node a, Node b);
};
}  // namespace sets
}  // namespace theory
}  // namespace cvc5

#endif
