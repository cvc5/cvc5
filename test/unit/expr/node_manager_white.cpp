/*********************                                                        */
/*! \file node_manager_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::NodeManager.
 **
 ** White box testing of CVC4::NodeManager.
 **/

#include <string>

#include "expr/node_manager.h"
#include "test_node.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {

using namespace CVC4::expr;

namespace test {

class TestNodeWhiteNodeManager : public TestNodeWhite
{
};

TEST_F(TestNodeWhiteNodeManager, mkConst_rational)
{
  Rational i("3");
  Node n = d_nodeManager->mkConst(i);
  Node m = d_nodeManager->mkConst(i);
  ASSERT_EQ(n.getId(), m.getId());
}

TEST_F(TestNodeWhiteNodeManager, oversized_node_builder)
{
  NodeBuilder<> nb;

  ASSERT_NO_THROW(nb.realloc(15));
  ASSERT_NO_THROW(nb.realloc(25));
  ASSERT_NO_THROW(nb.realloc(256));
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb.realloc(100), "toSize > d_nvMaxChildren");
#endif /* CVC4_ASSERTIONS */
  ASSERT_NO_THROW(nb.realloc(257));
  ASSERT_NO_THROW(nb.realloc(4000));
  ASSERT_NO_THROW(nb.realloc(20000));
  ASSERT_NO_THROW(nb.realloc(60000));
  ASSERT_NO_THROW(nb.realloc(65535));
  ASSERT_NO_THROW(nb.realloc(65536));
  ASSERT_NO_THROW(nb.realloc(67108863));
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb.realloc(67108863), "toSize > d_nvMaxChildren");
#endif /* CVC4_ASSERTIONS */
}

TEST_F(TestNodeWhiteNodeManager, topological_sort)
{
  TypeNode boolType = d_nodeManager->booleanType();
  Node i = d_nodeManager->mkSkolem("i", boolType);
  Node j = d_nodeManager->mkSkolem("j", boolType);
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
}  // namespace CVC4
