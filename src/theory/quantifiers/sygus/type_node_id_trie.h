/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type node identifier trie data structure.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__TYPE_NODE_ID_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__TYPE_NODE_ID_TRIE_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * A trie indexed by types that assigns unique identifiers to nodes based on
 * a vector of types.
 */
class TypeNodeIdTrie
{
 public:
  /** children of this node */
  std::map<TypeNode, TypeNodeIdTrie> d_children;
  /** the data stored at this node */
  std::vector<Node> d_data;
  /** add v to this trie, indexed by types */
  void add(Node v, std::vector<TypeNode>& types);
  /**
   * Assign each node in this trie an identifier such that
   * assign[v1] = assign[v2] iff v1 and v2 are indexed by the same values.
   */
  void assignIds(std::map<Node, unsigned>& assign, unsigned& idCount);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS__TYPE_NODE_ID_TRIE_H */
