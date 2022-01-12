/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of rewriter for arithmetic.
 */

#include "test_smt.h"
#include "util/rational.h"
#include "util/real_algebraic_number.h"

namespace cvc5 {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryArithRewriterBlack : public TestSmt
{
};

TEST_F(TestTheoryArithRewriterBlack, Rational)
{
  {
    Node a = d_nodeManager->mkConstReal(10);
    Node b = d_nodeManager->mkConstReal(-10);
    Node m = d_nodeManager->mkNode(Kind::ABS, a);
    Node n = d_nodeManager->mkNode(Kind::ABS, b);
    m = d_slvEngine->getRewriter()->rewrite(m);
    n = d_slvEngine->getRewriter()->rewrite(n);
    EXPECT_EQ(m, a);
    EXPECT_EQ(n, a);
  }
}

TEST_F(TestTheoryArithRewriterBlack, RealAlgebraicNumber)
{
  Trace.on("arith-rewriter");
  {
    RealAlgebraicNumber two({-8, 0, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(two);
    EXPECT_EQ(n.getKind(), Kind::CONST_RATIONAL);
    EXPECT_EQ(n.getConst<Rational>(), Rational(2));
  }
  {
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    n = d_nodeManager->mkNode(Kind::MULT, n, n);
    n = d_slvEngine->getRewriter()->rewrite(n);
    EXPECT_EQ(n.getKind(), Kind::CONST_RATIONAL);
    EXPECT_EQ(n.getConst<Rational>(), Rational(2));
  }
  {
    RealAlgebraicNumber twosqrt2({-8, 0, 1}, 2, 3);
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    n = d_nodeManager->mkNode(Kind::PLUS, n, n);
    n = d_slvEngine->getRewriter()->rewrite(n);
    EXPECT_EQ(n.getKind(), Kind::REAL_ALGEBRAIC_NUMBER);
    EXPECT_EQ(n.getOperator().getConst<RealAlgebraicNumber>(), twosqrt2);
  }
  {
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    n = d_nodeManager->mkNode(Kind::MINUS, n, n);
    n = d_slvEngine->getRewriter()->rewrite(n);
    EXPECT_EQ(n.getKind(), Kind::CONST_RATIONAL);
    EXPECT_EQ(n.getConst<Rational>(), Rational(0));
  }
  {
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    Node m = d_nodeManager->mkNode(
        Kind::PLUS, n, d_nodeManager->mkConstReal(Rational(1)));
    n = d_nodeManager->mkNode(Kind::MINUS, m, n);
    n = d_slvEngine->getRewriter()->rewrite(n);
    EXPECT_EQ(n.getKind(), Kind::CONST_RATIONAL);
    EXPECT_EQ(n.getConst<Rational>(), Rational(1));
  }
  {
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    RealAlgebraicNumber sqrt3({-3, 0, 1}, 1, 3);
    RealAlgebraicNumber sqrt10({-10, 0, 1}, 2, 4);
    Node n2 = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    Node n3 = d_nodeManager->mkRealAlgebraicNumber(sqrt3);
    Node n10 = d_nodeManager->mkRealAlgebraicNumber(sqrt10);
    {
      Node n = d_nodeManager->mkNode(
          Kind::LT, d_nodeManager->mkNode(Kind::PLUS, n2, n3), n10);
      n = d_slvEngine->getRewriter()->rewrite(n);
      EXPECT_EQ(n.getKind(), Kind::CONST_BOOLEAN);
      EXPECT_TRUE(n.getConst<bool>());
    }
    {
      Node n = d_nodeManager->mkNode(
          Kind::LT,
          d_nodeManager->mkNode(Kind::PLUS, n2, n3),
          d_nodeManager->mkNode(
              Kind::MINUS, n10, d_nodeManager->mkConstReal(Rational(1))));
      n = d_slvEngine->getRewriter()->rewrite(n);
      EXPECT_EQ(n.getKind(), Kind::CONST_BOOLEAN);
      EXPECT_FALSE(n.getConst<bool>());
    }
  }
}

}  // namespace test
}  // namespace cvc5
