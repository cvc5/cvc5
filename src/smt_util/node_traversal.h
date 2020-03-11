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

#include "cvc4_private.h"

#ifndef CVC4__SMT_UTIL__NODE_TRAVERSAL_H
#define CVC4__SMT_UTIL__NODE_TRAVERSAL_H

#include <cstddef>
#include <iterator>
#include <vector>

#include "expr/node.h"

namespace CVC4 {

// Iterator for traversing a node in post-order
// It does DAG-traversal, so indentical sub-nodes will be visited once only.
class NodePostorderIterator
{
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
  NodePostorderIterator(NodePostorderIterator&&) = default;
  NodePostorderIterator& operator=(NodePostorderIterator&&) = default;
  NodePostorderIterator(NodePostorderIterator&) = default;
  NodePostorderIterator& operator=(NodePostorderIterator&) = default;
  ~NodePostorderIterator() = default;

  // Preincrement
  NodePostorderIterator& operator++();
  // Postincrement
  NodePostorderIterator operator++(int);
  // Dereference
  reference operator*();
  // Equals
  bool operator==(const NodePostorderIterator&) const;
  // Not equals
  bool operator!=(const NodePostorderIterator&) const;

 private:
  // General Invariant: The top node on the stack (`d_stack.back()`) is the
  // current location of the traversal.
  //
  // There is one exception to this: when an iterator is constructed
  // (the stack has one node and nothing has been visited)
  //
  // While we could expand the stack, adding children until the top node is a
  // leaf, we do not do so, because this is expensive, and we want construction
  // to be cheap.
  std::vector<TNode> d_stack;

  // Whether (and how) we've visited a node.
  // Absent if we haven't visited it.
  // Set to `false` if we've pre-visited it (enqueued its children).
  // Set to `true` if we've also post-visited it.
  std::unordered_map<TNode, bool, TNodeHashFunction> d_visited;

  // Continues the traversal until the next post-visit.
  void advanceToNextPostVisit();

  // Return `true` iff this iterator has not been dereferenced or incremented
  // yet.
  bool justConstructed() const;
};

// Node wrapper that is iterable in DAG post-order
class NodePostorderIterable
{
 public:
  NodePostorderIterable(TNode n);

  // STL type definitions for an iterable
  using iterator = NodePostorderIterator;
  using value_type = TNode;
  using reference = TNode&;
  using difference_type = std::ptrdiff_t;

  // Move/copy construction and assignment. Destructor.
  NodePostorderIterable(NodePostorderIterable&&) = default;
  NodePostorderIterable& operator=(NodePostorderIterable&&) = default;
  NodePostorderIterable(NodePostorderIterable&) = default;
  NodePostorderIterable& operator=(NodePostorderIterable&) = default;
  ~NodePostorderIterable() = default;

  NodePostorderIterator begin();
  NodePostorderIterator end();

 private:
  TNode d_node;
};

}  // namespace CVC4

#endif  // CVC4__SMT_UTIL__NODE_TRAVERSAL_H
