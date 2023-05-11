/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Alex Ozdemir, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of node traversal iterators.
 */

#include <algorithm>
#include <cstddef>
#include <iterator>
#include <sstream>
#include <string>
#include <vector>

#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node_traversal.h"
#include "expr/node_value.h"
#include "test_node.h"

namespace cvc5::internal {

using namespace kind;

namespace test {

class TestNodeBlackNodeTraversalPostorder : public TestNode
{
};

class TestNodeBlackNodeTraversalPreorder : public TestNode
{
};

TEST_F(TestNodeBlackNodeTraversalPostorder, preincrement_iteration)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  auto traversal = NodeDfsIterable(cnd, VisitOrder::POSTORDER);
  NodeDfsIterator i = traversal.begin();
  NodeDfsIterator end = traversal.end();
  ASSERT_EQ(*i, tb);
  ASSERT_FALSE(i == end);
  ++i;
  ASSERT_EQ(*i, eb);
  ASSERT_FALSE(i == end);
  ++i;
  ASSERT_EQ(*i, cnd);
  ASSERT_FALSE(i == end);
  ++i;
  ASSERT_TRUE(i == end);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, postincrement_iteration)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  auto traversal = NodeDfsIterable(cnd, VisitOrder::POSTORDER);
  NodeDfsIterator i = traversal.begin();
  NodeDfsIterator end = traversal.end();
  ASSERT_EQ(*(i++), tb);
  ASSERT_EQ(*(i++), eb);
  ASSERT_EQ(*(i++), cnd);
  ASSERT_TRUE(i == end);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, postorder_is_default)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  auto traversal = NodeDfsIterable(cnd);
  NodeDfsIterator i = traversal.begin();
  NodeDfsIterator end = traversal.end();
  ASSERT_EQ(*i, tb);
  ASSERT_FALSE(i == end);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, range_for_loop)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  size_t count = 0;
  for (auto i : NodeDfsIterable(cnd, VisitOrder::POSTORDER))
  {
    ++count;
  }
  ASSERT_EQ(count, 3);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, count_if_with_loop)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  size_t count = 0;
  for (auto i : NodeDfsIterable(cnd, VisitOrder::POSTORDER))
  {
    if (i.isConst())
    {
      ++count;
    }
  }
  ASSERT_EQ(count, 2);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, stl_count_if)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  const Node top = d_nodeManager->mkNode(XOR, cnd, cnd);

  auto traversal = NodeDfsIterable(top, VisitOrder::POSTORDER);

  size_t count = std::count_if(
      traversal.begin(), traversal.end(), [](TNode n) { return n.isConst(); });
  ASSERT_EQ(count, 2);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, stl_copy)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  const Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
  std::vector<TNode> expected = {tb, eb, cnd, top};

  auto traversal = NodeDfsIterable(top, VisitOrder::POSTORDER);

  std::vector<TNode> actual;
  std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
  ASSERT_EQ(actual, expected);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, skip_if)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  const Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
  std::vector<TNode> expected = {top};

  auto traversal = NodeDfsIterable(
      top, VisitOrder::POSTORDER, [&cnd](TNode n) { return n == cnd; });

  std::vector<TNode> actual;
  std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
  ASSERT_EQ(actual, expected);
}

TEST_F(TestNodeBlackNodeTraversalPostorder, skip_all)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  const Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
  std::vector<TNode> expected = {};

  auto traversal =
      NodeDfsIterable(top, VisitOrder::POSTORDER, [](TNode n) { return true; });

  std::vector<TNode> actual;
  std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
  ASSERT_EQ(actual, expected);
}

TEST_F(TestNodeBlackNodeTraversalPreorder, preincrement_iteration)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  auto traversal = NodeDfsIterable(cnd, VisitOrder::PREORDER);
  NodeDfsIterator i = traversal.begin();
  NodeDfsIterator end = traversal.end();
  ASSERT_EQ(*i, cnd);
  ASSERT_FALSE(i == end);
  ++i;
  ASSERT_EQ(*i, tb);
  ASSERT_FALSE(i == end);
  ++i;
  ASSERT_EQ(*i, eb);
  ASSERT_FALSE(i == end);
  ++i;
  ASSERT_TRUE(i == end);
}

TEST_F(TestNodeBlackNodeTraversalPreorder, postincrement_iteration)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  auto traversal = NodeDfsIterable(cnd, VisitOrder::PREORDER);
  NodeDfsIterator i = traversal.begin();
  NodeDfsIterator end = traversal.end();
  ASSERT_EQ(*(i++), cnd);
  ASSERT_EQ(*(i++), tb);
  ASSERT_EQ(*(i++), eb);
  ASSERT_TRUE(i == end);
}

TEST_F(TestNodeBlackNodeTraversalPreorder, range_for_loop)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  size_t count = 0;
  for (auto i : NodeDfsIterable(cnd, VisitOrder::PREORDER))
  {
    ++count;
  }
  ASSERT_EQ(count, 3);
}

TEST_F(TestNodeBlackNodeTraversalPreorder, count_if_with_loop)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

  size_t count = 0;
  for (auto i : NodeDfsIterable(cnd, VisitOrder::PREORDER))
  {
    if (i.isConst())
    {
      ++count;
    }
  }
  ASSERT_EQ(count, 2);
}

TEST_F(TestNodeBlackNodeTraversalPreorder, stl_count_if)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  const Node top = d_nodeManager->mkNode(XOR, cnd, cnd);

  auto traversal = NodeDfsIterable(top, VisitOrder::PREORDER);

  size_t count = std::count_if(
      traversal.begin(), traversal.end(), [](TNode n) { return n.isConst(); });
  ASSERT_EQ(count, 2);
}

TEST_F(TestNodeBlackNodeTraversalPreorder, stl_copy)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  const Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
  std::vector<TNode> expected = {top, cnd, tb, eb};

  auto traversal = NodeDfsIterable(top, VisitOrder::PREORDER);

  std::vector<TNode> actual;
  std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
  ASSERT_EQ(actual, expected);
}

TEST_F(TestNodeBlackNodeTraversalPreorder, skip_if)
{
  const Node tb = d_nodeManager->mkConst(true);
  const Node eb = d_nodeManager->mkConst(false);
  const Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
  const Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
  std::vector<TNode> expected = {top, cnd, eb};

  auto traversal = NodeDfsIterable(
      top, VisitOrder::PREORDER, [&tb](TNode n) { return n == tb; });

  std::vector<TNode> actual;
  std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
  ASSERT_EQ(actual, expected);
}
}  // namespace test
}  // namespace cvc5::internal
