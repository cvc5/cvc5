/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Yoni Zohar, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of node_algorithm.{h,cpp}
 */

#include <string>
#include <vector>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "test_node.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace expr;
using namespace kind;

namespace test {

class TestNodeBlackNodeAlgorithm : public TestNode
{
};

TEST_F(TestNodeBlackNodeAlgorithm, get_symbols1)
{
  // The only symbol in ~x (x is a boolean varible) should be x
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->booleanType());
  Node n = d_nodeManager->mkNode(NOT, x);
  std::unordered_set<Node> syms;
  getSymbols(n, syms);
  ASSERT_EQ(syms.size(), 1);
  ASSERT_NE(syms.find(x), syms.end());
}

TEST_F(TestNodeBlackNodeAlgorithm, get_symbols2)
{
  // the only symbols in x=y ^ (exists var. var+var = x) are x and y, because
  // "var" is bound.

  // left conjunct
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->integerType());
  Node y = d_skolemManager->mkDummySkolem("y", d_nodeManager->integerType());
  Node left = d_nodeManager->mkNode(EQUAL, x, y);

  // right conjunct
  Node var = d_nodeManager->mkBoundVar(*d_intTypeNode);
  std::vector<Node> vars;
  vars.push_back(var);
  Node sum = d_nodeManager->mkNode(ADD, var, var);
  Node qeq = d_nodeManager->mkNode(EQUAL, x, sum);
  Node bvl = d_nodeManager->mkNode(BOUND_VAR_LIST, vars);
  Node right = d_nodeManager->mkNode(EXISTS, bvl, qeq);

  // conjunction
  Node res = d_nodeManager->mkNode(AND, left, right);

  // symbols
  std::unordered_set<Node> syms;
  getSymbols(res, syms);

  // assertions
  ASSERT_EQ(syms.size(), 2);
  ASSERT_NE(syms.find(x), syms.end());
  ASSERT_NE(syms.find(y), syms.end());
  ASSERT_EQ(syms.find(var), syms.end());
}

TEST_F(TestNodeBlackNodeAlgorithm, get_operators_map)
{
  // map to store result
  std::map<TypeNode, std::unordered_set<Node> > result =
      std::map<TypeNode, std::unordered_set<Node> >();

  // create test formula
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->integerType());
  Node plus = d_nodeManager->mkNode(ADD, x, x);
  Node mul = d_nodeManager->mkNode(MULT, x, x);
  Node eq1 = d_nodeManager->mkNode(EQUAL, plus, mul);

  Node y =
      d_skolemManager->mkDummySkolem("y", d_nodeManager->mkBitVectorType(4));
  Node ext1 = theory::bv::utils::mkExtract(y, 1, 0);
  Node ext2 = theory::bv::utils::mkExtract(y, 3, 2);
  Node eq2 = d_nodeManager->mkNode(EQUAL, ext1, ext2);

  Node formula = d_nodeManager->mkNode(AND, eq1, eq2);

  // call function
  expr::getOperatorsMap(formula, result);

  // Verify result
  // We should have only integer, bv and boolean as types
  ASSERT_EQ(result.size(), 3);
  ASSERT_NE(result.find(*d_intTypeNode), result.end());
  ASSERT_NE(result.find(*d_boolTypeNode), result.end());
  ASSERT_NE(result.find(*d_bvTypeNode), result.end());

  // in integers, we should only have plus and mult as operators
  ASSERT_EQ(result[*d_intTypeNode].size(), 2);
  ASSERT_NE(result[*d_intTypeNode].find(d_nodeManager->operatorOf(ADD)),
            result[*d_intTypeNode].end());
  ASSERT_NE(result[*d_intTypeNode].find(d_nodeManager->operatorOf(MULT)),
            result[*d_intTypeNode].end());

  // in booleans, we should only have "=" and "and" as an operator.
  ASSERT_EQ(result[*d_boolTypeNode].size(), 2);
  ASSERT_NE(result[*d_boolTypeNode].find(d_nodeManager->operatorOf(EQUAL)),
            result[*d_boolTypeNode].end());
  ASSERT_NE(result[*d_boolTypeNode].find(d_nodeManager->operatorOf(AND)),
            result[*d_boolTypeNode].end());

  // in bv, we should only have "extract" as an operator.
  ASSERT_EQ(result[*d_boolTypeNode].size(), 2);
  Node extractOp1 =
      d_nodeManager->mkConst<BitVectorExtract>(BitVectorExtract(1, 0));
  Node extractOp2 =
      d_nodeManager->mkConst<BitVectorExtract>(BitVectorExtract(3, 2));
  ASSERT_NE(result[*d_bvTypeNode].find(extractOp1),
            result[*d_bvTypeNode].end());
  ASSERT_NE(result[*d_bvTypeNode].find(extractOp2),
            result[*d_bvTypeNode].end());
}

TEST_F(TestNodeBlackNodeAlgorithm, match)
{
  TypeNode integer = d_nodeManager->integerType();

  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node two = d_nodeManager->mkConstInt(Rational(2));

  Node x = d_nodeManager->mkBoundVar(integer);
  Node a = d_skolemManager->mkDummySkolem("a", integer);

  Node n1 = d_nodeManager->mkNode(MULT, two, x);
  std::unordered_map<Node, Node> subs;

  // check reflexivity
  ASSERT_TRUE(match(n1, n1, subs));
  ASSERT_EQ(subs.size(), 0);

  Node n2 = d_nodeManager->mkNode(MULT, two, a);
  subs.clear();

  // check instance
  ASSERT_TRUE(match(n1, n2, subs));
  ASSERT_EQ(subs.size(), 1);
  ASSERT_EQ(subs[x], a);

  // should return false for flipped arguments (match is not symmetric)
  ASSERT_FALSE(match(n2, n1, subs));

  n2 = d_nodeManager->mkNode(MULT, one, a);

  // should return false since n2 is not an instance of n1
  ASSERT_FALSE(match(n1, n2, subs));

  n2 = d_nodeManager->mkNode(NONLINEAR_MULT, two, a);

  // should return false for similar operators
  ASSERT_FALSE(match(n1, n2, subs));

  n2 = d_nodeManager->mkNode(MULT, two, a, one);

  // should return false for different number of arguments
  ASSERT_FALSE(match(n1, n2, subs));

  n1 = x;
  n2 = d_nodeManager->mkConst(true);

  // should return false for different types
  ASSERT_FALSE(match(n1, n2, subs));

  n1 = d_nodeManager->mkNode(MULT, x, x);
  n2 = d_nodeManager->mkNode(MULT, two, a);

  // should return false for contradictory substitutions
  ASSERT_FALSE(match(n1, n2, subs));

  n2 = d_nodeManager->mkNode(MULT, a, a);
  subs.clear();

  // implementation: check if the cache works correctly
  ASSERT_TRUE(match(n1, n2, subs));
  ASSERT_EQ(subs.size(), 1);
  ASSERT_EQ(subs[x], a);
}
}  // namespace test
}  // namespace cvc5::internal
