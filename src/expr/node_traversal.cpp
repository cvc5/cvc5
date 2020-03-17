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

#include <iostream>

namespace CVC4 {

NodeDfsIterator::NodeDfsIterator(TNode n, bool postorder)
    : d_stack{n}, d_visited(), d_postorder(postorder)
{
}

NodeDfsIterator::NodeDfsIterator(bool postorder)
    : d_stack(), d_visited(), d_postorder(postorder)
{
}

NodeDfsIterator& NodeDfsIterator::operator++()
{
  std::cout << "post-increment: " << d_stack << std::endl;
  // If we were just constructed, advance to first visit
  advanceUntilVisitIfJustConstructed();

  // Advance past our current visit
  if (d_postorder)
  {
    finishPostVisit();
  }
  else
  {
    finishPreVisit();
  }

  // Make sure we're at an appropriate visit
  advanceUntilVisit();
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
  std::cout << "deref         : " << d_stack << std::endl;
  // If we were just constructed, advance to first visit
  advanceUntilVisitIfJustConstructed();

  return d_stack.back();
}

bool NodeDfsIterator::operator==(const NodeDfsIterator& other) const
{
  // The stack uniquely represents traversal state. We need not use the
  // scheduled node set. We also ignore the order: users should not compare
  // nodes of different order.
  return d_stack == other.d_stack;
}

bool NodeDfsIterator::operator!=(const NodeDfsIterator& other) const
{
  return !(*this == other);
}

void NodeDfsIterator::advance()
{
  Assert(!d_stack.empty());
  TNode back = d_stack.back();
  auto visitEntry = d_visited.find(back);
  if (visitEntry == d_visited.end())
  {
    // if we haven't pre-visited this node, pre-visit it
    finishPreVisit();
  }
  else if (visitEntry->second)
  {
    // if we've already post-visited this node: skip it
    d_stack.pop_back();
  }
  else
  {
    // otherwise, post-visit it
    finishPostVisit();
  }
}

void NodeDfsIterator::advanceUntilVisit()
{
  // While a node is enqueued ..
  while (d_postorder ? !atPostVisit() : !atPreVisit())
  {
    advance();
  }
}

void NodeDfsIterator::advanceUntilVisitIfJustConstructed()
{
  if (d_stack.size() == 1 && d_visited.size() == 0)
  {
    advanceUntilVisit();
  }
}

bool NodeDfsIterator::atPreVisit() const
{
  return d_stack.empty() || d_visited.count(d_stack.back()) == 0;
}

bool NodeDfsIterator::atPostVisit() const
{
  if (d_stack.empty())
  {
    return true;
  }
  auto visitEntry = d_visited.find(d_stack.back());

  // Have we pre-visited, but not post-visited, this node?
  return visitEntry != d_visited.end() && visitEntry->second == false;
}

void NodeDfsIterator::finishPreVisit()
{
  Assert(!d_stack.empty());
  Assert(atPreVisit());
  TNode back = d_stack.back();
  d_visited[back] = false;
  // Use integer underflow to reverse-iterate
  for (size_t n = back.getNumChildren(), i = n - 1; i < n; --i)
  {
    d_stack.push_back(back[i]);
  }
}

void NodeDfsIterator::finishPostVisit()
{
  Assert(!d_stack.empty());
  Assert(atPostVisit());
  d_visited[d_stack.back()] = true;
  d_stack.pop_back();
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
