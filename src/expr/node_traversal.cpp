/*********************                                                        */
/*! \file node_traversal.cpp
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

#include "node_traversal.h"

namespace CVC4 {

NodeDfsIterator::NodeDfsIterator(TNode n, bool postorder)
    : d_stack{n},
      d_visited(),
      d_postorder(postorder),
      d_initialized(false),
      d_current(TNode())
{
}

NodeDfsIterator::NodeDfsIterator(bool postorder)
    : d_stack(),
      d_visited(),
      d_postorder(postorder),
      d_initialized(true),
      d_current(TNode())
{
}

NodeDfsIterator& NodeDfsIterator::operator++()
{
  // If we were just constructed, advance to first visit
  initializeIfUninitialized();

  // Void our current visit, and advance to the next one
  d_current = TNode();
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
  Assert(d_initialized);

  return d_current;
}

bool NodeDfsIterator::operator==(const NodeDfsIterator& other) const
{
  // The stack and current node uniquely represent traversal state. We need not
  // use the scheduled node set. We also ignore the order: users should not
  // compare nodes of different order.
  return d_stack == other.d_stack && d_current == other.d_current;
}

bool NodeDfsIterator::operator!=(const NodeDfsIterator& other) const
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
      d_visited[back] = false;
      d_current = back;
      // Use integer underflow to reverse-iterate
      for (size_t n = back.getNumChildren(), i = n - 1; i < n; --i)
      {
        d_stack.push_back(back[i]);
      }
      if (!d_postorder)
      {
        return;
      }
    }
    else if (!d_postorder || visitEntry->second)
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
}

void NodeDfsIterator::initializeIfUninitialized()
{
  if (!d_initialized)
  {
    advanceToNextVisit();
    d_initialized = true;
  }
}

void NodeDfsIterator::finishPreVisit()
{
  Assert(!d_stack.empty());
  TNode back = d_stack.back();
  d_visited[back] = false;
  // Use integer underflow to reverse-iterate
  for (size_t n = back.getNumChildren(), i = n - 1; i < n; --i)
  {
    d_stack.push_back(back[i]);
  }
}

NodeDfsIterable::NodeDfsIterable(TNode n) : d_node(n), d_postorder(true) {}

NodeDfsIterable& NodeDfsIterable::in_postorder()
{
  d_postorder = true;
  return *this;
}

NodeDfsIterable& NodeDfsIterable::in_preorder()
{
  d_postorder = false;
  return *this;
}

NodeDfsIterator NodeDfsIterable::begin() const
{
  return NodeDfsIterator(d_node, d_postorder);
}

NodeDfsIterator NodeDfsIterable::end() const
{
  return NodeDfsIterator(d_postorder);
}

}  // namespace CVC4
