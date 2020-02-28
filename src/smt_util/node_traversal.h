/*********************                                                        */
/*! \file node_traversal.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Iterators for traversing nodes.
 **/

#include <cstddef>
#include "cvc4_private.h"

#ifndef CVC4__SMT_UTIL__NODE_TRAVERSAL_H
#define CVC4__SMT_UTIL__NODE_TRAVERSAL_H

#include <cstddef>
#include <iterator>
#include <vector>

#include "expr/node.h"

namespace CVC4 {

// Iterator for traversing a node in post-order
class NodePostorderIterator {
public:
  // Construct a traversal iterator beginning at `n`
  NodePostorderIterator(TNode n);
  // Construct an end-of-traversal iterator
  NodePostorderIterator();

  // STL type definitions for an iterator
  using value_type = TNode;
  using pointer = TNode*;
  using reference = TNode&;
  using iterator_category = std::forward_iterator_tag;
  using difference_type = std::ptrdiff_t;

  // Move/copy construction and assignment. Destructor.
  NodePostorderIterator(NodePostorderIterator &&) = default;
  NodePostorderIterator& operator=(NodePostorderIterator &&) = default;
  NodePostorderIterator(NodePostorderIterator &) = default;
  NodePostorderIterator& operator=(NodePostorderIterator &) = default;
  ~NodePostorderIterator() = default;

  // Preincrement
  NodePostorderIterator& operator++();
  // Postincrement
  NodePostorderIterator operator++(int);
  // Dereference
  reference operator*();
  // Equals
  bool operator==(const NodePostorderIterator&) const;
  // Equals
  bool operator!=(const NodePostorderIterator&) const;

private:

  // The next thing on the stack is the next thing to visit.
  // If it is associated with `false`, then its children haven't been visited yet, and we visit them first.
  // If it is associated with `true`, then we visit it.
  // Invariant: the top (back) node is always associated with `true`.
  std::vector<std::pair<bool, TNode>> d_stack;

  // Adds the children of the top node (on the stack) to the stack, until the
  // top node is a leaf
  void enqueueChildrenUntilLeaf();

};

// Node wrapper that is iterable in post-order
class NodePostorderIterable {
public:
  NodePostorderIterable(TNode n);

  // STL type definitions for an iterable
  using iterator = NodePostorderIterator;
  using value_type = TNode;
  using reference = TNode;
  using difference_type = std::ptrdiff_t;

  // Move/copy construction and assignment. Destructor.
  NodePostorderIterable(NodePostorderIterable &&) = default;
  NodePostorderIterable& operator=(NodePostorderIterable &&) = default;
  NodePostorderIterable(NodePostorderIterable &) = default;
  NodePostorderIterable& operator=(NodePostorderIterable &) = default;
  ~NodePostorderIterable() = default;

  NodePostorderIterator begin();
  NodePostorderIterator end();
private:
  TNode d_node;
};

}/* CVC4 namespace */

#endif // CVC4__SMT_UTIL__NODE_TRAVERSAL_H
