/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryArithRewriterBlack : public TestSmt
{
};

TEST_F(TestTheoryArithRewriterBlack, RealAlgebraicNumber)
{
  {
    RealAlgebraicNumber two({-8, 0, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(two);
    EXPECT_EQ(n.isConst(), true);
    EXPECT_EQ(n.getConst<Rational>(), Rational(2));
  }
  {
    RealAlgebraicNumber twosqrt2({-8, 0, 1}, 2, 3);
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    n = d_nodeManager->mkNode(Kind::ADD, n, n);
    n = d_slvEngine->getEnv().getRewriter()->rewrite(n);
    EXPECT_EQ(n.getKind(), Kind::REAL_ALGEBRAIC_NUMBER);
    EXPECT_EQ(n.getOperator().getConst<RealAlgebraicNumber>(), twosqrt2);
  }
  {
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    n = d_nodeManager->mkNode(Kind::MULT, n, n);
    n = d_slvEngine->getEnv().getRewriter()->rewrite(n);
    EXPECT_EQ(n.isConst(), true);
    EXPECT_EQ(n.getConst<Rational>(), Rational(2));
  }
  {
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    n = d_nodeManager->mkNode(Kind::SUB, n, n);
    n = d_slvEngine->getEnv().getRewriter()->rewrite(n);
    EXPECT_EQ(n.isConst(), true);
    EXPECT_EQ(n.getConst<Rational>(), Rational(0));
  }
  {
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
    Node m = d_nodeManager->mkRealAlgebraicNumber(msqrt2);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    Node mm = d_nodeManager->mkNode(Kind::NEG, m);
    Node mn = d_nodeManager->mkNode(Kind::NEG, n);
    mm = d_slvEngine->getEnv().getRewriter()->rewrite(mm);
    mn = d_slvEngine->getEnv().getRewriter()->rewrite(mn);
    EXPECT_EQ(-msqrt2, sqrt2);
    EXPECT_EQ(-sqrt2, msqrt2);
    EXPECT_EQ(mm, n);
    EXPECT_EQ(mn, m);
  }
}

TEST_F(TestTheoryArithRewriterBlack, Abs)
{
  {
    Node a = d_nodeManager->mkConstReal(10);
    Node b = d_nodeManager->mkConstReal(-10);
    Node m = d_nodeManager->mkNode(Kind::ABS, a);
    Node n = d_nodeManager->mkNode(Kind::ABS, b);
    m = d_slvEngine->getEnv().getRewriter()->rewrite(m);
    n = d_slvEngine->getEnv().getRewriter()->rewrite(n);
    EXPECT_EQ(m, a);
    EXPECT_EQ(n, a);
  }
  {
    Node a = d_nodeManager->mkConstReal(Rational(3,2));
    Node b = d_nodeManager->mkConstReal(Rational(-3,2));
    Node m = d_nodeManager->mkNode(Kind::ABS, a);
    Node n = d_nodeManager->mkNode(Kind::ABS, b);
    m = d_slvEngine->getEnv().getRewriter()->rewrite(m);
    n = d_slvEngine->getEnv().getRewriter()->rewrite(n);
    EXPECT_EQ(m, a);
    EXPECT_EQ(n, a);
  }
  {
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
    Node a = d_nodeManager->mkRealAlgebraicNumber(msqrt2);
    Node b = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    Node m = d_nodeManager->mkNode(Kind::ABS, a);
    Node n = d_nodeManager->mkNode(Kind::ABS, b);
    m = d_slvEngine->getEnv().getRewriter()->rewrite(m);
    n = d_slvEngine->getEnv().getRewriter()->rewrite(n);
    EXPECT_EQ(m, b);
    EXPECT_EQ(n, b);
  }
}

}  // namespace test
}  // namespace cvc5::internal
