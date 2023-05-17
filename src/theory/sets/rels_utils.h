/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace theory {
namespace sets {

class RelsUtils
{
 public:
  /**
   * compute the transitive closure of a binary relation
   * @param members constant nodes of type (Tuple E E) that are known to in the
   * relation rel
   * @param rel a binary relation of type (Relation E E)
   * @pre all members need to be constants
   * @return the transitive closure of the relation
   */
  static std::set<Node> computeTC(const std::set<Node>& members, Node rel);

  /**
   * add all pairs (a, c) to the transitive closures where c is reachable from b
   * in the transitive relation in a depth first search manner.
   * @param rel a binary relation of type (Relation E E)
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
   * @param rel a node of type (Relation E E)
   * @param a a node of type E
   * @param b a node of type E
   * @return  a tuple (tuple a b)
   */
  static Node constructPair(Node rel, Node a, Node b);

  /**
   * @param n of the form ((_ rel.group (n_1 ... n_k) ) A) where A is a
   * constant relation
   * @return a partition of A such that each part contains tuples with the same
   * projection with indices n_1 ... n_k
   */
  static Node evaluateGroup(TNode n);

  /**
   * @param n has the form ((_ rel.aggr n1 ... n_k) f initial A)
   * where initial and A are constants
   * @return the aggregation result.
   */
  static Node evaluateRelationAggregate(TNode n);
};
}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif
