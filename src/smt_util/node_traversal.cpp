#include "node_traversal.h"

#include <iostream>

namespace CVC4 {

NodeDagIterator::NodeDagIterator(TNode n, bool postorder)
    : d_stack{n}, d_visited(), d_postorder(postorder)
{
}

NodeDagIterator::NodeDagIterator(bool postorder)
    : d_stack(), d_visited(), d_postorder(postorder)
{
}

NodeDagIterator& NodeDagIterator::operator++()
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

NodeDagIterator NodeDagIterator::operator++(int)
{
  NodeDagIterator copyOfOld(*this);
  ++*this;
  return copyOfOld;
}

TNode& NodeDagIterator::operator*()
{
  std::cout << "deref         : " << d_stack << std::endl;
  // If we were just constructed, advance to first visit
  advanceUntilVisitIfJustConstructed();

  return d_stack.back();
}

bool NodeDagIterator::operator==(const NodeDagIterator& other) const
{
  // The stack uniquely represents traversal state. We need not use the
  // scheduled node set. We also ignore the order: users should not compare
  // nodes of different order.
  return d_stack == other.d_stack;
}

bool NodeDagIterator::operator!=(const NodeDagIterator& other) const
{
  return !(*this == other);
}

void NodeDagIterator::advance()
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

void NodeDagIterator::advanceUntilVisit()
{
  // While a node is enqueued ..
  while (d_postorder ? !atPostVisit() : !atPreVisit())
  {
    advance();
  }
}

void NodeDagIterator::advanceUntilVisitIfJustConstructed()
{
  if (d_stack.size() == 1 && d_visited.size() == 0)
  {
    advanceUntilVisit();
  }
}

bool NodeDagIterator::atPreVisit() const
{
  return d_stack.empty() || d_visited.count(d_stack.back()) == 0;
}

bool NodeDagIterator::atPostVisit() const
{
  if (d_stack.empty())
  {
    return true;
  }
  auto visitEntry = d_visited.find(d_stack.back());

  // Have we pre-visited, but not post-visited, this node?
  return visitEntry != d_visited.end() && visitEntry->second == false;
}

void NodeDagIterator::finishPreVisit()
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

void NodeDagIterator::finishPostVisit()
{
  Assert(!d_stack.empty());
  Assert(atPostVisit());
  d_visited[d_stack.back()] = true;
  d_stack.pop_back();
}

NodeDagIterable::NodeDagIterable(TNode n) : d_node(n), d_postorder(true) {}

NodeDagIterable& NodeDagIterable::in_postorder()
{
  d_postorder = true;
  return *this;
}

NodeDagIterable& NodeDagIterable::in_preorder()
{
  d_postorder = false;
  return *this;
}

NodeDagIterator NodeDagIterable::begin()
{
  return NodeDagIterator(d_node, d_postorder);
}

NodeDagIterator NodeDagIterable::end() { return NodeDagIterator(d_postorder); }

}  // namespace CVC4
