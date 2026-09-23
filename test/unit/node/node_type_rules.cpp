/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of type rules for cvc5::Node.
 */

#include <cvc5/cvc5.h>

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

#include "expr/node_manager.h"
#include "expr/type_node.h"
#include "test_node.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

class TestNodeTestRules : public TestNode
{
 protected:
  TypeNode getTypeConcat(NodeManager* nm, const Node& a, const Node& b)
  {
    Node c = nm->mkNode(Kind::STRING_CONCAT, a, b);
    return c.getTypeOrNull(true);
  }
};

TEST_F(TestNodeTestRules, gradual_types)
{
  std::unique_ptr<NodeManager> nm(std::make_unique<NodeManager>());
  TypeNode at = nm->mkAbstractType(Kind::ABSTRACT_TYPE);
  TypeNode aseqt = nm->mkAbstractType(Kind::SEQUENCE_TYPE);
  TypeNode intt = nm->integerType();
  TypeNode sit = nm->mkSequenceType(intt);

  SkolemManager* sm = nm->getSkolemManager();
  Node kat = sm->mkDummySkolem("kat", at);
  Node kaseqt = sm->mkDummySkolem("kaseqt", aseqt);
  Node ksit = sm->mkDummySkolem("ksit", sit);
  Node one = nm->mkConstInt(Rational(1));

  TypeNode t1 = getTypeConcat(nm.get(), kat, kat);
  ASSERT_TRUE(t1 == at);
  TypeNode t2 = getTypeConcat(nm.get(), kat, kaseqt);
  ASSERT_TRUE(t2 == aseqt);
  TypeNode t3 = getTypeConcat(nm.get(), kat, ksit);
  ASSERT_TRUE(t3 == sit);
  TypeNode t4 = getTypeConcat(nm.get(), kat, one);
  ASSERT_TRUE(t4.isNull());
}

TEST_F(TestNodeTestRules, builtin_operator)
{
  Node op = d_nodeManager->operatorOf(Kind::ADD);
  ASSERT_EQ(op.getType(), d_nodeManager->builtinOperatorType());
  ASSERT_EQ(op.getType(true), d_nodeManager->builtinOperatorType());
}

TEST_F(TestNodeTestRules, type_computation_child_failure)
{
  Node b = d_nodeManager->mkVar("b", *d_boolTypeNode);
  Node x = d_nodeManager->mkVar("x", *d_intTypeNode);
  // These branches have no common type, even without full type checking.
  Node ite = d_nodeManager->mkNode(Kind::ITE, b, b, x);
  Node equality = d_nodeManager->mkNode(Kind::EQUAL, ite, ite);
  Node negation = d_nodeManager->mkNode(Kind::NOT, equality);
  ASSERT_TRUE(negation.getTypeOrNull().isNull());
  ASSERT_TRUE(negation.getTypeOrNull(true).isNull());
}

TEST_F(TestNodeTestRules, type_check_after_computation)
{
  Node x = d_nodeManager->mkVar("x", *d_intTypeNode);
  Node b = d_nodeManager->mkVar("b", *d_boolTypeNode);
  Node equality = d_nodeManager->mkNode(Kind::EQUAL, x, b);
  Node negation = d_nodeManager->mkNode(Kind::NOT, equality);
  // Computing a type must not mark it as checked: checking the cached Boolean
  // type still needs to detect the incompatible equality operands.
  ASSERT_EQ(negation.getType(), *d_boolTypeNode);
  ASSERT_TRUE(negation.getTypeOrNull(true).isNull());

  Node sum = d_nodeManager->mkNode(Kind::ADD, x, x);
  Node valid = d_nodeManager->mkNode(Kind::EQUAL, sum, x);
  ASSERT_EQ(valid.getType(), *d_boolTypeNode);
  ASSERT_EQ(valid.getType(true), *d_boolTypeNode);
  ASSERT_EQ(valid.getType(), *d_boolTypeNode);
}

}  // namespace test
}  // namespace cvc5::internal
