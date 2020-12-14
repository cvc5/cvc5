/*********************                                                        */
/*! \file attribute_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Attribute.
 **
 ** Black box testing of CVC4::Attribute.
 **/

#include <sstream>
#include <vector>

#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_value.h"
#include "test_expr.h"

namespace CVC4 {

using namespace kind;
using namespace smt;

namespace test {

class TestExprBlackAttribute : public TestExprBlack
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

TEST_F(TestExprBlackAttribute, ints)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));
  const uint64_t val = 63489;
  uint64_t data0 = 0;
  uint64_t data1 = 0;

  PrimitiveIntAttribute attr;
  ASSERT_FALSE(node->getAttribute(attr, data0));
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  EXPECT_EQ(data1, val);

  delete node;
}

TEST_F(TestExprBlackAttribute, tnodes)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

  Node val(d_nodeManager->mkSkolem("b", booleanType));
  TNode data0;
  TNode data1;

  TNodeAttribute attr;
  ASSERT_FALSE(node->getAttribute(attr, data0));
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  EXPECT_EQ(data1, val);

  delete node;
}

TEST_F(TestExprBlackAttribute, strings)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

  std::string val("63489");
  std::string data0;
  std::string data1;

  StringAttribute attr;
  ASSERT_FALSE(node->getAttribute(attr, data0));
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  EXPECT_EQ(data1, val);

  delete node;
}

TEST_F(TestExprBlackAttribute, bools)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

  bool val = true;
  bool data0 = false;
  bool data1 = false;

  BoolAttribute attr;
  ASSERT_TRUE(node->getAttribute(attr, data0));
  EXPECT_EQ(false, data0);
  node->setAttribute(attr, val);
  ASSERT_TRUE(node->getAttribute(attr, data1));
  EXPECT_EQ(data1, val);

  delete node;
}

}  // namespace test
}  // namespace CVC4
