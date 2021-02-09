/*********************                                                        */
/*! \file node_manager_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Christopher L. Conway, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::NodeManager.
 **
 ** Black box testing of CVC4::NodeManager.
 **/

#include <string>
#include <vector>

#include "base/output.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "test_node.h"
#include "test_utils.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {

using namespace kind;
using namespace expr;

namespace test {

class TestNodeBlackNodeManager : public TestNodeBlack
{
};

TEST_F(TestNodeBlackNodeManager, mkNode_not)
{
  Node x = d_nodeManager->mkSkolem("x", d_nodeManager->booleanType());
  Node n = d_nodeManager->mkNode(NOT, x);
  ASSERT_EQ(n.getNumChildren(), 1u);
  ASSERT_EQ(n.getKind(), NOT);
  ASSERT_EQ(n[0], x);
}

TEST_F(TestNodeBlackNodeManager, mkNode_binary)
{
  Node x = d_nodeManager->mkSkolem("x", d_nodeManager->booleanType());
  Node y = d_nodeManager->mkSkolem("y", d_nodeManager->booleanType());
  Node n = d_nodeManager->mkNode(IMPLIES, x, y);
  ASSERT_EQ(n.getNumChildren(), 2u);
  ASSERT_EQ(n.getKind(), IMPLIES);
  ASSERT_EQ(n[0], x);
  ASSERT_EQ(n[1], y);
}

TEST_F(TestNodeBlackNodeManager, mkNode_three_children)
{
  Node x = d_nodeManager->mkSkolem("x", d_nodeManager->booleanType());
  Node y = d_nodeManager->mkSkolem("y", d_nodeManager->booleanType());
  Node z = d_nodeManager->mkSkolem("z", d_nodeManager->booleanType());
  Node n = d_nodeManager->mkNode(AND, x, y, z);
  ASSERT_EQ(n.getNumChildren(), 3u);
  ASSERT_EQ(n.getKind(), AND);
  ASSERT_EQ(n[0], x);
  ASSERT_EQ(n[1], y);
  ASSERT_EQ(n[2], z);
}

TEST_F(TestNodeBlackNodeManager, mkNode_four_children)
{
  Node x1 = d_nodeManager->mkSkolem("x1", d_nodeManager->booleanType());
  Node x2 = d_nodeManager->mkSkolem("x2", d_nodeManager->booleanType());
  Node x3 = d_nodeManager->mkSkolem("x3", d_nodeManager->booleanType());
  Node x4 = d_nodeManager->mkSkolem("x4", d_nodeManager->booleanType());
  Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4);
  ASSERT_EQ(n.getNumChildren(), 4u);
  ASSERT_EQ(n.getKind(), AND);
  ASSERT_EQ(n[0], x1);
  ASSERT_EQ(n[1], x2);
  ASSERT_EQ(n[2], x3);
  ASSERT_EQ(n[3], x4);
}

TEST_F(TestNodeBlackNodeManager, mkNode_five_children)
{
  Node x1 = d_nodeManager->mkSkolem("x1", d_nodeManager->booleanType());
  Node x2 = d_nodeManager->mkSkolem("x2", d_nodeManager->booleanType());
  Node x3 = d_nodeManager->mkSkolem("x3", d_nodeManager->booleanType());
  Node x4 = d_nodeManager->mkSkolem("x4", d_nodeManager->booleanType());
  Node x5 = d_nodeManager->mkSkolem("x5", d_nodeManager->booleanType());
  Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4, x5);
  ASSERT_EQ(n.getNumChildren(), 5u);
  ASSERT_EQ(n.getKind(), AND);
  ASSERT_EQ(n[0], x1);
  ASSERT_EQ(n[1], x2);
  ASSERT_EQ(n[2], x3);
  ASSERT_EQ(n[3], x4);
  ASSERT_EQ(n[4], x5);
}

TEST_F(TestNodeBlackNodeManager, mkNode_vector_of_node)
{
  Node x1 = d_nodeManager->mkSkolem("x1", d_nodeManager->booleanType());
  Node x2 = d_nodeManager->mkSkolem("x2", d_nodeManager->booleanType());
  Node x3 = d_nodeManager->mkSkolem("x3", d_nodeManager->booleanType());
  std::vector<Node> args;
  args.push_back(x1);
  args.push_back(x2);
  args.push_back(x3);
  Node n = d_nodeManager->mkNode(AND, args);
  ASSERT_EQ(n.getNumChildren(), args.size());
  ASSERT_EQ(n.getKind(), AND);
  for (unsigned i = 0; i < args.size(); ++i)
  {
    ASSERT_EQ(n[i], args[i]);
  }
}

TEST_F(TestNodeBlackNodeManager, mkNode_vector_of_tnode)
{
  Node x1 = d_nodeManager->mkSkolem("x1", d_nodeManager->booleanType());
  Node x2 = d_nodeManager->mkSkolem("x2", d_nodeManager->booleanType());
  Node x3 = d_nodeManager->mkSkolem("x3", d_nodeManager->booleanType());
  std::vector<TNode> args;
  args.push_back(x1);
  args.push_back(x2);
  args.push_back(x3);
  Node n = d_nodeManager->mkNode(AND, args);
  ASSERT_EQ(n.getNumChildren(), args.size());
  ASSERT_EQ(n.getKind(), AND);
  for (unsigned i = 0; i < args.size(); ++i)
  {
    ASSERT_EQ(n[i], args[i]);
  }
}

TEST_F(TestNodeBlackNodeManager, mkSkolem_with_name)
{
  Node x = d_nodeManager->mkSkolem(
      "x", *d_boolTypeNode, "", NodeManager::SKOLEM_EXACT_NAME);
  ASSERT_EQ(x.getKind(), SKOLEM);
  ASSERT_EQ(x.getNumChildren(), 0u);
  ASSERT_EQ(x.getAttribute(VarNameAttr()), "x");
  ASSERT_EQ(x.getType(), *d_boolTypeNode);
}

TEST_F(TestNodeBlackNodeManager, mkConst_bool)
{
  Node tt = d_nodeManager->mkConst(true);
  ASSERT_EQ(tt.getConst<bool>(), true);
  Node ff = d_nodeManager->mkConst(false);
  ASSERT_EQ(ff.getConst<bool>(), false);
}

TEST_F(TestNodeBlackNodeManager, mkConst_rational)
{
  Rational r("3/2");
  Node n = d_nodeManager->mkConst(r);
  ASSERT_EQ(n.getConst<Rational>(), r);
}

TEST_F(TestNodeBlackNodeManager, hasOperator)
{
  ASSERT_TRUE(NodeManager::hasOperator(AND));
  ASSERT_TRUE(NodeManager::hasOperator(OR));
  ASSERT_TRUE(NodeManager::hasOperator(NOT));
  ASSERT_TRUE(NodeManager::hasOperator(APPLY_UF));
  ASSERT_TRUE(!NodeManager::hasOperator(VARIABLE));
}

TEST_F(TestNodeBlackNodeManager, booleanType)
{
  TypeNode t = d_nodeManager->booleanType();
  TypeNode t2 = d_nodeManager->booleanType();
  TypeNode t3 = d_nodeManager->mkSort("T");
  ASSERT_TRUE(t.isBoolean());
  ASSERT_FALSE(t.isFunction());
  ASSERT_FALSE(t.isNull());
  ASSERT_FALSE(t.isPredicate());
  ASSERT_FALSE(t.isSort());
  ASSERT_EQ(t, t2);
  ASSERT_NE(t, t3);

  TypeNode bt = t;
  ASSERT_EQ(bt, t);
}

TEST_F(TestNodeBlackNodeManager, mkFunctionType_bool_to_bool)
{
  TypeNode booleanType = d_nodeManager->booleanType();
  TypeNode t = d_nodeManager->mkFunctionType(booleanType, booleanType);
  TypeNode t2 = d_nodeManager->mkFunctionType(booleanType, booleanType);

  ASSERT_FALSE(t.isBoolean());
  ASSERT_TRUE(t.isFunction());
  ASSERT_FALSE(t.isNull());
  ASSERT_TRUE(t.isPredicate());
  ASSERT_FALSE(t.isSort());

  ASSERT_EQ(t, t2);

  TypeNode ft = t;
  ASSERT_EQ(ft, t);
  ASSERT_EQ(ft.getArgTypes().size(), 1u);
  ASSERT_EQ(ft.getArgTypes()[0], booleanType);
  ASSERT_EQ(ft.getRangeType(), booleanType);
}

TEST_F(TestNodeBlackNodeManager, mkFunctionType_vector_args_with_return_type)
{
  TypeNode a = d_nodeManager->mkSort();
  TypeNode b = d_nodeManager->mkSort();
  TypeNode c = d_nodeManager->mkSort();

  std::vector<TypeNode> argTypes;
  argTypes.push_back(a);
  argTypes.push_back(b);

  TypeNode t = d_nodeManager->mkFunctionType(argTypes, c);
  TypeNode t2 = d_nodeManager->mkFunctionType(argTypes, c);

  ASSERT_FALSE(t.isBoolean());
  ASSERT_TRUE(t.isFunction());
  ASSERT_FALSE(t.isNull());
  ASSERT_FALSE(t.isPredicate());
  ASSERT_FALSE(t.isSort());

  ASSERT_EQ(t, t2);

  TypeNode ft = t;
  ASSERT_EQ(ft, t);
  ASSERT_EQ(ft.getArgTypes().size(), argTypes.size());
  ASSERT_EQ(ft.getArgTypes()[0], a);
  ASSERT_EQ(ft.getArgTypes()[1], b);
  ASSERT_EQ(ft.getRangeType(), c);
}

TEST_F(TestNodeBlackNodeManager, mkFunctionType_vector_of_arguments)
{
  TypeNode a = d_nodeManager->mkSort();
  TypeNode b = d_nodeManager->mkSort();
  TypeNode c = d_nodeManager->mkSort();

  std::vector<TypeNode> types;
  types.push_back(a);
  types.push_back(b);
  types.push_back(c);

  TypeNode t = d_nodeManager->mkFunctionType(types);
  TypeNode t2 = d_nodeManager->mkFunctionType(types);

  ASSERT_FALSE(t.isBoolean());
  ASSERT_TRUE(t.isFunction());
  ASSERT_FALSE(t.isNull());
  ASSERT_FALSE(t.isPredicate());
  ASSERT_FALSE(t.isSort());

  ASSERT_EQ(t, t2);

  TypeNode ft = t;
  ASSERT_EQ(ft, t);
  ASSERT_EQ(ft.getArgTypes().size(), types.size() - 1);
  ASSERT_EQ(ft.getArgTypes()[0], a);
  ASSERT_EQ(ft.getArgTypes()[1], b);
  ASSERT_EQ(ft.getRangeType(), c);
}

TEST_F(TestNodeBlackNodeManager, mkPredicateType)
{
  TypeNode a = d_nodeManager->mkSort("a");
  TypeNode b = d_nodeManager->mkSort("b");
  TypeNode c = d_nodeManager->mkSort("c");
  TypeNode booleanType = d_nodeManager->booleanType();

  std::vector<TypeNode> argTypes;
  argTypes.push_back(a);
  argTypes.push_back(b);
  argTypes.push_back(c);

  TypeNode t = d_nodeManager->mkPredicateType(argTypes);
  TypeNode t2 = d_nodeManager->mkPredicateType(argTypes);

  ASSERT_FALSE(t.isBoolean());
  ASSERT_TRUE(t.isFunction());
  ASSERT_FALSE(t.isNull());
  ASSERT_TRUE(t.isPredicate());
  ASSERT_FALSE(t.isSort());

  ASSERT_EQ(t, t2);

  TypeNode ft = t;
  ASSERT_EQ(ft, t);
  ASSERT_EQ(ft.getArgTypes().size(), argTypes.size());
  ASSERT_EQ(ft.getArgTypes()[0], a);
  ASSERT_EQ(ft.getArgTypes()[1], b);
  ASSERT_EQ(ft.getArgTypes()[2], c);
  ASSERT_EQ(ft.getRangeType(), booleanType);
}

/* This test is only valid if assertions are enabled. */
TEST_F(TestNodeBlackNodeManager, mkNode_too_few_children)
{
#ifdef CVC4_ASSERTIONS
  Node x = d_nodeManager->mkSkolem("x", d_nodeManager->booleanType());
  ASSERT_DEATH(d_nodeManager->mkNode(AND, x),
               "Nodes with kind AND must have at least 2 children");
#endif
}

/* This test is only valid if assertions are enabled. */
TEST_F(TestNodeBlackNodeManager, mkNode_too_many_children)
{
#ifdef CVC4_ASSERTIONS
  std::vector<Node> vars;
  const unsigned int max = metakind::getUpperBoundForKind(AND);
  TypeNode boolType = d_nodeManager->booleanType();
  Node skolem_i = d_nodeManager->mkSkolem("i", boolType);
  Node skolem_j = d_nodeManager->mkSkolem("j", boolType);
  Node andNode = skolem_i.andNode(skolem_j);
  Node orNode = skolem_i.orNode(skolem_j);
  while (vars.size() <= max)
  {
    vars.push_back(andNode);
    vars.push_back(skolem_j);
    vars.push_back(orNode);
  }
  ASSERT_DEATH(d_nodeManager->mkNode(AND, vars), "toSize > d_nvMaxChildren");
#endif
}
}  // namespace test
}  // namespace CVC4
