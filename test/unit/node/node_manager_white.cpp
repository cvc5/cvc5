/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
using namespace cvc5::internal::kind;

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
  NodeBuilder nb;

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
  Node n1 = d_nodeManager->mkNode(kind::AND, j, j);
  Node n2 = d_nodeManager->mkNode(kind::AND, i, n1);

  {
    std::vector<NodeValue*> roots = {n1.d_nv};
    ASSERT_EQ(NodeManager::TopologicalSort(roots), roots);
  }

  {
    std::vector<NodeValue*> roots = {n2.d_nv, n1.d_nv};
    std::vector<NodeValue*> result = {n1.d_nv, n2.d_nv};
    ASSERT_EQ(NodeManager::TopologicalSort(roots), result);
  }
}
}  // namespace test
}  // namespace cvc5::internal
