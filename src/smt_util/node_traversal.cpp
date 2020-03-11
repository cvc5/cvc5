#include "node_traversal.h"

namespace CVC4 {

NodePostorderIterator::NodePostorderIterator(TNode n) : d_stack{n}, d_visited()
{
}

NodePostorderIterator::NodePostorderIterator() : d_stack(), d_visited() {}

NodePostorderIterator& NodePostorderIterator::operator++()
{
  if (justConstructed())
  {
    advanceToNextPostVisit();
  }
  if (d_stack.size() > 0)
  {
    d_stack.pop_back();
    advanceToNextPostVisit();
  }
  return *this;
}

NodePostorderIterator NodePostorderIterator::operator++(int)
{
  NodePostorderIterator copyOfOld(*this);
  ++*this;
  return copyOfOld;
}

TNode& NodePostorderIterator::operator*()
{
  if (justConstructed())
  {
    advanceToNextPostVisit();
  }
  return d_stack.back();
}

bool NodePostorderIterator::operator==(const NodePostorderIterator& other) const
{
  // The stack uniquely represents traversal state. We need not use the
  // scheduled node set.
  return d_stack == other.d_stack;
}

bool NodePostorderIterator::operator!=(const NodePostorderIterator& other) const
{
  return !(*this == other);
}

void NodePostorderIterator::advanceToNextPostVisit()
{
  // While a node is enqueued ..
  while (d_stack.size() > 0)
  {
    TNode back = d_stack.back();
    auto visitEntry = d_visited.find(back);
    if (visitEntry == d_visited.end())
    {
      // if we haven't pre-visited this node: enqueue its children
      d_visited[back] = false;
      // (use underflow wrapping to reverse-iterate)
      for (size_t n = back.getNumChildren(), i = n - 1; i < n; --i)
      {
        d_stack.push_back(back[i]);
      }
    }
    else if (visitEntry->second)
    {
      // if we've already post-visited this node: skip it
      d_stack.pop_back();
    }
    else
    {
      // otherwise, it's time to post-visit it: stop here!
      visitEntry->second = true;
      return;
    }
  }
}

bool NodePostorderIterator::justConstructed() const
{
  return d_stack.size() == 1 && d_visited.size() == 0;
}

NodePostorderIterable::NodePostorderIterable(TNode n) : d_node(n) {}

NodePostorderIterator NodePostorderIterable::begin()
{
  return NodePostorderIterator(d_node);
}

NodePostorderIterator NodePostorderIterable::end()
{
  return NodePostorderIterator();
}

}  // namespace CVC4
