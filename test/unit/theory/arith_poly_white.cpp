/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

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
  Node zero = d_nodeManager->mkConstReal(Rational(0));
  Node one = d_nodeManager->mkConstReal(Rational(1));
  Node two = d_nodeManager->mkConstReal(Rational(2));
  Node x = d_nodeManager->mkVar("x", intType);
  Node y = d_nodeManager->mkVar("y", intType);
  Node z = d_nodeManager->mkVar("z", intType);
  Node w = d_nodeManager->mkVar("w", intType);

  Node t1, t2;

  t1 = zero;
  t2 = one;
  ASSERT_FALSE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(ADD, x, y);
  t2 = d_nodeManager->mkNode(ADD, y, d_nodeManager->mkNode(MULT, one, x));
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t2 = d_nodeManager->mkNode(ADD, x, x, y);
  ASSERT_FALSE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(ADD, x, d_nodeManager->mkNode(MULT, y, zero));
  t2 = x;
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT, y, d_nodeManager->mkNode(ADD, one, one));
  t2 = d_nodeManager->mkNode(ADD, y, y);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT,
                             d_nodeManager->mkNode(ADD, one, zero),
                             d_nodeManager->mkNode(ADD, x, y));
  t2 = d_nodeManager->mkNode(ADD, x, y);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(ADD, {x, y, z, w, y});
  t2 = d_nodeManager->mkNode(ADD, {w, y, y, z, x});
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(SUB, t1, t2);
  t2 = zero;
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(NEG, d_nodeManager->mkNode(ADD, x, y));
  t2 = d_nodeManager->mkNode(SUB, zero, d_nodeManager->mkNode(ADD, y, x));
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT, d_nodeManager->mkNode(NEG, x), y);
  t2 = d_nodeManager->mkNode(MULT, d_nodeManager->mkNode(NEG, y), x);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(MULT, x, d_nodeManager->mkNode(ADD, y, z));
  t2 = d_nodeManager->mkNode(ADD,
                             d_nodeManager->mkNode(MULT, x, y),
                             d_nodeManager->mkNode(MULT, z, x));
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));
}

TEST_F(TestTheoryWhiteArithPolyNorm, check_poly_norm_real)
{
  TypeNode realType = d_nodeManager->realType();
  Node zero = d_nodeManager->mkConstReal(Rational(0));
  Node one = d_nodeManager->mkConstReal(Rational(1));
  Node half = d_nodeManager->mkConstReal(Rational(1) / Rational(2));
  Node two = d_nodeManager->mkConstReal(Rational(2));
  Node x = d_nodeManager->mkVar("x", realType);
  Node y = d_nodeManager->mkVar("y", realType);

  Node t1, t2;

  t1 = d_nodeManager->mkNode(ADD, x, y, y);
  t2 = d_nodeManager->mkNode(ADD, y, x, y);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = one;
  t2 = d_nodeManager->mkNode(MULT, two, half);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));

  t1 = d_nodeManager->mkNode(ADD, y, x);
  t2 = d_nodeManager->mkNode(
      MULT,
      d_nodeManager->mkNode(ADD,
                            d_nodeManager->mkNode(MULT, half, x),
                            d_nodeManager->mkNode(MULT, half, y)),
      two);
  ASSERT_TRUE(PolyNorm::isArithPolyNorm(t1, t2));
}

}  // namespace test
}  // namespace cvc5::internal
