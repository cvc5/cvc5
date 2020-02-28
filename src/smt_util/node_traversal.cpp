#include "node_traversal.h"

namespace CVC4 {

NodePostorderIterator::NodePostorderIterator(TNode n)
  : d_stack{{false, n}}
{
  enqueueChildrenUntilLeaf();
}

NodePostorderIterator::NodePostorderIterator()
  : d_stack() {}

NodePostorderIterator& NodePostorderIterator::operator++()
{
    if (d_stack.size() > 0) {
      d_stack.pop_back();
      enqueueChildrenUntilLeaf();
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
  return d_stack.back().second;
}

bool NodePostorderIterator::operator==(const NodePostorderIterator& other) const
{
  return d_stack == other.d_stack;
}

bool NodePostorderIterator::operator!=(const NodePostorderIterator& other) const
{
  return !(*this == other);
}

void NodePostorderIterator::enqueueChildrenUntilLeaf()
{
  if (d_stack.size() > 0) {
    // While the top element does not have its children enqueued,
    while (!d_stack.back().first) {
      d_stack.back().first = true;
      TNode back = d_stack.back().second;
      // use integer underflow wrapping behavior to reverse-iterate over the children,
      for (size_t i = back.getNumChildren() - 1; i < back.getNumChildren(); --i)
      {
        // and enqueue them.
        d_stack.emplace_back(false, back[i]);
      }
    }
  }
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

}
