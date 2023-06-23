/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::Attribute.
 */

#include <sstream>
#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_value.h"
#include "test_node.h"

namespace cvc5::internal {

using namespace kind;
using namespace smt;

namespace test {

class TestNodeBlackAttribute : public TestNode
{
 protected:
  struct PrimitiveIntAttributeId
  {
  };
  using PrimitiveIntAttribute =
      expr::Attribute<PrimitiveIntAttributeId, uint64_t>;
  struct TNodeAttributeId
  {
  };
  using TNodeAttribute = expr::Attribute<TNodeAttributeId, TNode>;
  struct StringAttributeId
  {
  };
  using StringAttribute = expr::Attribute<StringAttributeId, std::string>;
  struct BoolAttributeId
  {
  };
  using BoolAttribute = expr::Attribute<BoolAttributeId, bool>;
};

TEST_F(TestNodeBlackAttribute, ints)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_skolemManager->mkDummySkolem("b", booleanType));
  const uint64_t val = 63489;
  uint64_t data0 = 0;
  uint64_t data1 = 0;

  PrimitiveIntAttribute attr;
  ASSERT_FALSE(node->getAttribute(attr, data0));
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  ASSERT_EQ(data1, val);

  delete node;
}

TEST_F(TestNodeBlackAttribute, tnodes)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_skolemManager->mkDummySkolem("b", booleanType));

  Node val(d_skolemManager->mkDummySkolem("b", booleanType));
  TNode data0;
  TNode data1;

  TNodeAttribute attr;
  ASSERT_FALSE(node->getAttribute(attr, data0));
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  ASSERT_EQ(data1, val);

  delete node;
}

TEST_F(TestNodeBlackAttribute, strings)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_skolemManager->mkDummySkolem("b", booleanType));

  std::string val("63489");
  std::string data0;
  std::string data1;

  StringAttribute attr;
  ASSERT_FALSE(node->getAttribute(attr, data0));
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  ASSERT_EQ(data1, val);

  delete node;
}

TEST_F(TestNodeBlackAttribute, bools)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_skolemManager->mkDummySkolem("b", booleanType));

  bool val = true;
  bool data0 = false;
  bool data1 = false;

  BoolAttribute attr;
  ASSERT_TRUE(node->getAttribute(attr, data0));
  ASSERT_EQ(false, data0);
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  ASSERT_EQ(data1, val);

  delete node;
}

}  // namespace test
}  // namespace cvc5::internal
