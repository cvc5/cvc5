/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::NodeManager.
 */

#include <string>

#include "expr/node_manager.h"
#include "test_node.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace cvc5::internal::expr;

namespace test {

class TestNodeWhiteNodeManager : public TestNode
{
};

TEST_F(TestNodeWhiteNodeManager, mkConst_rational)
{
  Rational i("3");
  Node n = d_nodeManager->mkConstInt(i);
  Node m = d_nodeManager->mkConstInt(i);
  ASSERT_EQ(n.getId(), m.getId());
}

TEST_F(TestNodeWhiteNodeManager, oversized_node_builder)
{
  NodeBuilder nb(d_nodeManager.get());

  ASSERT_NO_THROW(nb.realloc(15));
  ASSERT_NO_THROW(nb.realloc(25));
  ASSERT_NO_THROW(nb.realloc(256));
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb.realloc(100), "toSize > d_nvMaxChildren");
#endif /* CVC5_ASSERTIONS */
  ASSERT_NO_THROW(nb.realloc(257));
  ASSERT_NO_THROW(nb.realloc(4000));
  ASSERT_NO_THROW(nb.realloc(20000));
  ASSERT_NO_THROW(nb.realloc(60000));
  ASSERT_NO_THROW(nb.realloc(65535));
  ASSERT_NO_THROW(nb.realloc(65536));
  ASSERT_NO_THROW(nb.realloc(67108863));
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb.realloc(67108863), "toSize > d_nvMaxChildren");
#endif /* CVC5_ASSERTIONS */
}

TEST_F(TestNodeWhiteNodeManager, topological_sort)
{
  TypeNode boolType = d_nodeManager->booleanType();
  Node i = d_skolemManager->mkDummySkolem("i", boolType);
  Node j = d_skolemManager->mkDummySkolem("j", boolType);
  Node n1 = d_nodeManager->mkNode(Kind::AND, j, j);
  Node n2 = d_nodeManager->mkNode(Kind::AND, i, n1);

  {
    std::vector<NodeValue*> roots = {n1.d_nv};
    ASSERT_EQ(NodeManager::TopologicalSort(roots), roots);
  }

  {
    std::vector<NodeValue*> roots = {n2.d_nv, n1.d_nv};
    std::vector<NodeValue*> result = {n1.d_nv, n2.d_nv};
    ASSERT_EQ(NodeManager::TopologicalSort(roots), result);
  }

  {
    TypeNode intType = d_nodeManager->integerType();
    TypeNode fnType = d_nodeManager->mkFunctionType(intType, intType);
    Node f = d_skolemManager->mkDummySkolem("f", fnType);
    Node x = d_skolemManager->mkDummySkolem("x", intType);
    Node fx = d_nodeManager->mkNode(Kind::APPLY_UF, f, x);
    std::vector<NodeValue*> roots = {fx.d_nv, f.d_nv};
    std::vector<NodeValue*> result = {f.d_nv, fx.d_nv};
    ASSERT_EQ(NodeManager::TopologicalSort(roots), result);
  }
}

TEST_F(TestNodeWhiteNodeManager, reclaim_zombies_transitively)
{
  // Build the chain n_1 = (not x), ..., n_depth = (not n_{depth-1}), in which
  // each node is only referenced by its parent. Once the chain is released,
  // only n_depth is a zombie.
  const size_t depth = 10;
  const size_t mid = depth / 2;
  Node x = d_skolemManager->mkDummySkolem("x", *d_boolTypeNode);
  uint64_t midId = 0;
  {
    Node n = x;
    for (size_t i = 1; i <= depth; ++i)
    {
      n = d_nodeManager->mkNode(Kind::NOT, n);
      if (i == mid)
      {
        midId = n.getId();
      }
    }
  }
  // Create and release enough nodes to exceed the zombie threshold (5000, see
  // NodeManager::markForDeletion()), which triggers a single collection pass.
  {
    std::vector<Node> nodes;
    for (size_t i = 0; i <= 5000; ++i)
    {
      nodes.push_back(d_nodeManager->mkConstInt(Rational(i)));
    }
  }
  // The pass must have reclaimed the whole chain, not only n_depth, so
  // rebuilding n_mid creates a new node instead of finding the old one.
  Node n = x;
  for (size_t i = 1; i <= mid; ++i)
  {
    n = d_nodeManager->mkNode(Kind::NOT, n);
  }
  ASSERT_NE(n.getId(), midId);
}
}  // namespace test
}  // namespace cvc5::internal
