/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Variadic trie utility
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__VARIADIC_TRIE_H
#define CVC5__EXPR__VARIADIC_TRIE_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {

/**
 * A trie that stores data at undetermined depth. Storing data at
 * undetermined depth is in contrast to the NodeTrie (expr/node_trie.h), which
 * assumes all data is stored at a fixed depth.
 *
 * Since data can be stored at any depth, we require both a d_children field
 * and a d_data field.
 */
class VariadicTrie
{
 public:
  /** the children of this node */
  std::map<Node, VariadicTrie> d_children;
  /** the data at this node */
  Node d_data;
  /**
   * Add data with identifier n indexed by i, return true if data is not already
   * stored at the node indexed by i.
   */
  bool add(Node n, const std::vector<Node>& i);
  /** Is there any data in this trie that is indexed by any subset of is? */
  bool hasSubset(const std::vector<Node>& is) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__VARIADIC_TRIE_H */
