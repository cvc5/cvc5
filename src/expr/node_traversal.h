/*********************                                                        */
/*! \file node_traversal.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Iterators for traversing nodes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__NODE_TRAVERSAL_H
#define CVC4__EXPR__NODE_TRAVERSAL_H

#include <cstddef>
#include <functional>
#include <iterator>
#include <unordered_map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {

/**
 * Enum that represents an order in which nodes are visited.
 */
enum class VisitOrder
{
  PREORDER,
  POSTORDER
};

// Iterator for traversing a node in pre-/post-order
// It does DAG-traversal, so indentical sub-nodes will be visited once only.
class NodeDfsIterator
{
 public:
  // STL type definitions for an iterator
  using value_type = TNode;
  using pointer = TNode*;
  using reference = TNode&;
  using iterator_category = std::forward_iterator_tag;
  using difference_type = std::ptrdiff_t;

  // Construct a traversal iterator beginning at `n`
  NodeDfsIterator(TNode n, VisitOrder order, std::function<bool(TNode)> skipIf);
  // Construct an end-of-traversal iterator
  NodeDfsIterator(VisitOrder order);

  // Move/copy construction and assignment. Destructor.
  NodeDfsIterator(NodeDfsIterator&&) = default;
  NodeDfsIterator& operator=(NodeDfsIterator&&) = default;
  NodeDfsIterator(NodeDfsIterator&) = default;
  NodeDfsIterator& operator=(NodeDfsIterator&) = default;
  ~NodeDfsIterator() = default;

  // Preincrement
  NodeDfsIterator& operator++();
  // Postincrement
  NodeDfsIterator operator++(int);
  // Dereference
  reference operator*();
  // Equals
  bool operator==(const NodeDfsIterator&) const;
  // Not equals
  bool operator!=(const NodeDfsIterator&) const;

 private:
  // While we're not at an appropriate visit (see d_postorder), advance.
  // In each step:
  //   * enqueue children of a not-yet-pre-visited node (and mark it
  //     previsited)
  //   * pop a not-yet-post-visited node (and mark it post-visited)
  //   * pop an already post-visited node.
  // After calling this, `d_current` will be changed to the next node, if there
  // is another node in the traversal.
  void advanceToNextVisit();

  // If this iterator hasn't been dereferenced or incremented yet, advance to
  // first visit.
  // Necessary because we are lazy and don't find our first visit node at
  // construction time.
  void initializeIfUninitialized();

  // Stack of nodes to visit.
  std::vector<TNode> d_stack;

  // Whether (and how) we've visited a node.
  // Absent if we haven't visited it.
  // Set to `false` if we've already pre-visited it (enqueued its children).
  // Set to `true` if we've also already post-visited it.
  std::unordered_map<TNode, bool, TNodeHashFunction> d_visited;

  // The visit order that this iterator is using
  VisitOrder d_order;

  // Current referent node. A valid node to visit if non-null.
  // Null after construction (but before first access) and at the end.
  TNode d_current;

  // When to omit a node and its descendants from the traversal
  std::function<bool(TNode)> d_skipIf;
};

// Node wrapper that is iterable in DAG pre-/post-order
class NodeDfsIterable
{
 public:
  /**
   * Creates a new node wrapper that can be used to iterate over the children
   * of a node in pre-/post-order.
   *
   * @param n The node the iterate
   * @param order The order in which the children are visited.
   * @param skipIf Function that determines whether a given node and its
   *               descendants should be skipped or not.
   */
  NodeDfsIterable(
      TNode n,
      VisitOrder order = VisitOrder::POSTORDER,
      std::function<bool(TNode)> skipIf = [](TNode) { return false; });

  // Move/copy construction and assignment. Destructor.
  NodeDfsIterable(NodeDfsIterable&&) = default;
  NodeDfsIterable& operator=(NodeDfsIterable&&) = default;
  NodeDfsIterable(NodeDfsIterable&) = default;
  NodeDfsIterable& operator=(NodeDfsIterable&) = default;
  ~NodeDfsIterable() = default;

  NodeDfsIterator begin() const;
  NodeDfsIterator end() const;

 private:
  TNode d_node;
  VisitOrder d_order;
  std::function<bool(TNode)> d_skipIf;
};

}  // namespace CVC4

#endif  // CVC4__EXPR__NODE_TRAVERSAL_H
