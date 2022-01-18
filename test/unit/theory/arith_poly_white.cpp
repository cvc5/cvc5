/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for arithmetic polynomial normalization.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "test_smt.h"
#include "theory/arith/arith_poly_norm.h"
#include "util/rational.h"

namespace cvc5 {

using namespace theory;
using namespace theory::arith;
using namespace kind;

namespace test {

class TestTheoryWhiteArithPolyNorm : public TestSmt
{
 protected:
  void SetUp() override { TestSmt::SetUp(); }
};

TEST_F(TestTheoryWhiteArithPolyNorm, check_poly_norm_int)
{
  TypeNode intType = d_nodeManager->integerType();
  Node zero = d_nodeManager->mkConst(CONST_RATIONAL, Rational(0));
  Node one = d_nodeManager->mkConst(CONST_RATIONAL, Rational(1));
  Node two = d_nodeManager->mkConst(CONST_RATIONAL, Rational(2));
  Node x = d_nodeManager->mkVar("x", intType);
  Node y = d_nodeManager->mkVar("y", intType);
  Node z = d_nodeManager->mkVar("z", intType);
  Node w = d_nodeManager->mkVar("w", intType);

  Node t1, t2;

  t1 = zero;
  t2 = one;
  ASSERT_FALSE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(PLUS, x, y);
  t2 = d_nodeManager->mkNode(PLUS, y, d_nodeManager->mkNode(MULT, one, x));
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t2 = d_nodeManager->mkNode(PLUS, x, x, y);
  ASSERT_FALSE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(PLUS, x, d_nodeManager->mkNode(MULT, y, zero));
  t2 = x;
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT, y, d_nodeManager->mkNode(PLUS, one, one));
  t2 = d_nodeManager->mkNode(PLUS, y, y);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT,
                             d_nodeManager->mkNode(PLUS, one, zero),
                             d_nodeManager->mkNode(PLUS, x, y));
  t2 = d_nodeManager->mkNode(PLUS, x, y);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(PLUS, {x, y, z, w, y});
  t2 = d_nodeManager->mkNode(PLUS, {w, y, y, z, x});
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MINUS, t1, t2);
  t2 = zero;
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(UMINUS, d_nodeManager->mkNode(PLUS, x, y));
  t2 = d_nodeManager->mkNode(MINUS, zero, d_nodeManager->mkNode(PLUS, y, x));
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT, d_nodeManager->mkNode(UMINUS, x), y);
  t2 = d_nodeManager->mkNode(MULT, d_nodeManager->mkNode(UMINUS, y), x);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT, x, d_nodeManager->mkNode(PLUS, y, z));
  t2 = d_nodeManager->mkNode(PLUS,
                             d_nodeManager->mkNode(MULT, x, y),
                             d_nodeManager->mkNode(MULT, z, x));
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));
}

TEST_F(TestTheoryWhiteArithPolyNorm, check_poly_norm_real)
{
  TypeNode realType = d_nodeManager->realType();
  Node zero = d_nodeManager->mkConst(CONST_RATIONAL, Rational(0));
  Node one = d_nodeManager->mkConst(CONST_RATIONAL, Rational(1));
  Node half = d_nodeManager->mkConst(CONST_RATIONAL, Rational(1) / Rational(2));
  Node two = d_nodeManager->mkConst(CONST_RATIONAL, Rational(2));
  Node x = d_nodeManager->mkVar("x", realType);
  Node y = d_nodeManager->mkVar("y", realType);

  Node t1, t2;

  t1 = d_nodeManager->mkNode(PLUS, x, y, y);
  t2 = d_nodeManager->mkNode(PLUS, y, x, y);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = one;
  t2 = d_nodeManager->mkNode(MULT, two, half);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(PLUS, y, x);
  t2 = d_nodeManager->mkNode(
      MULT,
      d_nodeManager->mkNode(PLUS,
                            d_nodeManager->mkNode(MULT, half, x),
                            d_nodeManager->mkNode(MULT, half, y)),
      two);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));
}

}  // namespace test
}  // namespace cvc5
