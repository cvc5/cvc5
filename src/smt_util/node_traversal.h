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
class NodeDagIterator
{
 public:
  // Construct a traversal iterator beginning at `n`
  NodeDagIterator(TNode n, bool postorder);
  // Construct an end-of-traversal iterator
  NodeDagIterator(bool postorder);

  // STL type definitions for an iterator
  using value_type = TNode;
  using pointer = TNode*;
  using reference = TNode&;
  using iterator_category = std::forward_iterator_tag;
  using difference_type = std::ptrdiff_t;

  // Move/copy construction and assignment. Destructor.
  NodeDagIterator(NodeDagIterator&&) = default;
  NodeDagIterator& operator=(NodeDagIterator&&) = default;
  NodeDagIterator(NodeDagIterator&) = default;
  NodeDagIterator& operator=(NodeDagIterator&) = default;
  ~NodeDagIterator() = default;

  // Preincrement
  NodeDagIterator& operator++();
  // Postincrement
  NodeDagIterator operator++(int);
  // Dereference
  reference operator*();
  // Equals
  bool operator==(const NodeDagIterator&) const;
  // Not equals
  bool operator!=(const NodeDagIterator&) const;

 private:
  // Advance one step.
  // Options:
  //   * enqueue children of a not-yet-pre-visited node (and mark it
  //     previsited)
  //   * pop a not-yet-post-visited node (and mark it post-visited)
  //   * pop an already post-visited node.
  void advance();

  // While we're not at an appropriate visit (see d_postorder), advance.
  void advanceUntilVisit();

  // If this iterator hasn't been dereferenced or incremented yet, advance to
  // first visit.
  // Necessary because we break the "top of stack is current visit" invariant
  // during construction to keep construction cheap. See `d_stack`.
  void advanceUntilVisitIfJustConstructed();

  // Whether the current state is a pre-visit
  bool atPreVisit() const;
  // Whether the current state is a post-visit
  bool atPostVisit() const;
  // Step past a pre-visit: record it and enqueue children
  void finishPreVisit();
  // Step past a post-visit: record it and pop the node
  void finishPostVisit();

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
  // Set to `false` if we've already pre-visited it (enqueued its children).
  // Set to `true` if we've also already post-visited it.
  std::unordered_map<TNode, bool, TNodeHashFunction> d_visited;

  // Whether this is a post-order iterator (the alternative is pre-order)
  //
  bool d_postorder;
};

// Node wrapper that is iterable in DAG post-order
class NodeDagIterable
{
 public:
  NodeDagIterable(TNode n);

  // STL type definitions for an iterable
  using iterator = NodeDagIterator;
  using value_type = TNode;
  using reference = TNode&;
  using difference_type = std::ptrdiff_t;

  // Modifying the traversal order

  // Modify this iterable to be in post-order (default)
  NodeDagIterable& in_postorder();
  // Modify this iterable to be in pre-order
  NodeDagIterable& in_preorder();

  // Move/copy construction and assignment. Destructor.
  NodeDagIterable(NodeDagIterable&&) = default;
  NodeDagIterable& operator=(NodeDagIterable&&) = default;
  NodeDagIterable(NodeDagIterable&) = default;
  NodeDagIterable& operator=(NodeDagIterable&) = default;
  ~NodeDagIterable() = default;

  NodeDagIterator begin() const;
  NodeDagIterator end() const;

 private:
  TNode d_node;
  bool d_postorder;
};

}  // namespace CVC4

#endif  // CVC4__SMT_UTIL__NODE_TRAVERSAL_H
