/*********************                                                        */
/*! \file node_traversal.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Iterators for traversing nodes.
 **/

#include "node_traversal.h"

namespace CVC4 {

NodeDfsIterator::NodeDfsIterator(TNode n,
                                 VisitOrder order,
                                 std::function<bool(TNode)> skipIf)
    : d_stack{n},
      d_visited(),
      d_order(order),
      d_current(TNode()),
      d_skipIf(skipIf)
{
}

NodeDfsIterator::NodeDfsIterator(VisitOrder order)
    : d_stack(),
      d_visited(),
      d_order(order),
      d_current(TNode()),
      d_skipIf([](TNode) { return false; })
{
}

NodeDfsIterator& NodeDfsIterator::operator++()
{
  // If we were just constructed, advance to first visit, **before**
  // advancing past it to the next visit (below).
  initializeIfUninitialized();

  // Advance to the next visit
  advanceToNextVisit();
  return *this;
}

NodeDfsIterator NodeDfsIterator::operator++(int)
{
  NodeDfsIterator copyOfOld(*this);
  ++*this;
  return copyOfOld;
}

TNode& NodeDfsIterator::operator*()
{
  // If we were just constructed, advance to first visit
  initializeIfUninitialized();
  Assert(!d_current.isNull());

  return d_current;
}

bool NodeDfsIterator::operator==(NodeDfsIterator& other)
{
  // Unitialize this node, and the other, before comparing.
  initializeIfUninitialized();
  other.initializeIfUninitialized();
  // The stack and current node uniquely represent traversal state. We need not
  // use the scheduled node set.
  //
  // Users should not compare iterators for traversals of different nodes, or
  // traversals with different skipIfs.
  Assert(d_order == other.d_order);
  return d_stack == other.d_stack && d_current == other.d_current;
}

bool NodeDfsIterator::operator!=(NodeDfsIterator& other)
{
  return !(*this == other);
}

void NodeDfsIterator::advanceToNextVisit()
{
  // While a node is enqueued and we're not at the right visit type
  while (!d_stack.empty())
  {
    TNode back = d_stack.back();
    auto visitEntry = d_visited.find(back);
    if (visitEntry == d_visited.end())
    {
      // if we haven't pre-visited this node, pre-visit it
      if (d_skipIf(back))
      {
        // actually, skip it if the skip predicate says so...
        d_stack.pop_back();
        continue;
      }
      d_visited[back] = false;
      d_current = back;
      // Use integer underflow to reverse-iterate
      for (size_t n = back.getNumChildren(), i = n - 1; i < n; --i)
      {
        d_stack.push_back(back[i]);
      }
      if (d_order == VisitOrder::PREORDER)
      {
        return;
      }
    }
    else if (d_order == VisitOrder::PREORDER || visitEntry->second)
    {
      // if we're previsiting or we've already post-visited this node: skip it
      d_stack.pop_back();
    }
    else
    {
      // otherwise, this is a post-visit
      visitEntry->second = true;
      d_current = back;
      d_stack.pop_back();
      return;
    }
  }
  // We're at the end of the traversal: nullify the current node to agree
  // with the "end" iterator.
  d_current = TNode();
}

void NodeDfsIterator::initializeIfUninitialized()
{
  if (d_current.isNull())
  {
    advanceToNextVisit();
  }
}

NodeDfsIterable::NodeDfsIterable(TNode n,
                                 VisitOrder order,
                                 std::function<bool(TNode)> skipIf)
    : d_node(n), d_order(order), d_skipIf(skipIf)
{
}

NodeDfsIterator NodeDfsIterable::begin() const
{
  return NodeDfsIterator(d_node, d_order, d_skipIf);
}

NodeDfsIterator NodeDfsIterable::end() const
{
  return NodeDfsIterator(d_order);
}

}  // namespace CVC4
