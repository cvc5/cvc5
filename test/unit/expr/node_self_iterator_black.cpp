/*********************                                                        */
/*! \file node_self_iterator_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::expr::NodeSelfIterator
 **
 ** Black box testing of CVC4::expr::NodeSelfIterator
 **/

#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_self_iterator.h"
#include "test_node.h"

namespace CVC4 {

using namespace kind;
using namespace expr;

namespace test {

class TestNodeBlackNodeSelfIterator : public TestNodeBlack
{
};

TEST_F(TestNodeBlackNodeSelfIterator, iteration)
{
  Node x = d_nodeManager->mkSkolem("x", *d_boolTypeNode);
  Node y = d_nodeManager->mkSkolem("y", *d_boolTypeNode);
  Node x_and_y = x.andNode(y);
  NodeSelfIterator i = x_and_y, j = NodeSelfIterator::self(x_and_y);
  ASSERT_NE(i, x_and_y.end());
  ASSERT_NE(j, x_and_y.end());
  ASSERT_EQ(*i, x_and_y);
  ASSERT_EQ(*j, x_and_y);
  ASSERT_EQ(*i++, x_and_y);
  ASSERT_EQ(*j++, x_and_y);
  ASSERT_EQ(i, NodeSelfIterator::selfEnd(x_and_y));
  ASSERT_EQ(j, NodeSelfIterator::selfEnd(x_and_y));
  ASSERT_EQ(i, x_and_y.end());
  ASSERT_EQ(j, x_and_y.end());

  i = x_and_y.begin();
  ASSERT_NE(i, x_and_y.end());
  ASSERT_EQ(*i, x);
  ASSERT_EQ(*++i, y);
  ASSERT_EQ(++i, x_and_y.end());
}
}  // namespace test
}  // namespace CVC4
