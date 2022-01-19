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
    n = d_nodeManager->mkNode(Kind::MULT, n, n);
    n = d_slvEngine->getRewriter()->rewrite(n);
    EXPECT_EQ(n.getKind(), Kind::CONST_RATIONAL);
    EXPECT_EQ(n.getConst<Rational>(), Rational(2));
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
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
    Node m = d_nodeManager->mkRealAlgebraicNumber(msqrt2);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    Node mm = d_nodeManager->mkNode(Kind::UMINUS, m);
    Node mn = d_nodeManager->mkNode(Kind::UMINUS, n);
    mm = d_slvEngine->getRewriter()->rewrite(mm);
    mn = d_slvEngine->getRewriter()->rewrite(mn);
    EXPECT_EQ(-msqrt2, sqrt2);
    EXPECT_EQ(-sqrt2, msqrt2);
    EXPECT_EQ(mm, n);
    EXPECT_EQ(mn, m);
  }
}

/**
 * Return n! / (k! * (n-k)!). Tries to avoid overflows by keeping the
 * intermediate values small.
 */
uint64_t binomial(uint64_t n, uint64_t k)
{
  uint64_t result = 1;
  uint64_t nextmult = k + 1;
  uint64_t nextdiv = 2;
  while (nextmult <= n || nextdiv <= n - k)
  {
    while (nextdiv <= n - k && result % nextdiv == 0)
    {
      result /= nextdiv;
      ++nextdiv;
    }
    if (nextmult <= n)
    {
      result *= nextmult;
      ++nextmult;
    }
  }
  return result;
}

TEST_F(TestTheoryArithRewriterBlack, distribute)
{
  {
    constexpr size_t n = 40;
    Node a = d_nodeManager->mkBoundVar("a", d_nodeManager->realType());
    Node b = d_nodeManager->mkBoundVar("b", d_nodeManager->realType());
    Node sum = d_nodeManager->mkNode(Kind::PLUS, a, b);
    Node prod = d_nodeManager->mkNode(Kind::MULT, std::vector<Node>(n, sum));
    prod = d_slvEngine->getRewriter()->rewrite(prod);

    std::vector<Node> reference;
    for (size_t k = 0; k <= n; ++k)
    {
      std::vector<Node> mult;
      mult.insert(mult.end(), n - k, a);
      mult.insert(mult.end(), k, b);
      Node mon = d_nodeManager->mkNode(Kind::NONLINEAR_MULT, std::move(mult));
      Rational fac = binomial(n, k);
      if (!fac.isOne())
      {
        mon = d_nodeManager->mkNode(
            Kind::MULT, d_nodeManager->mkConstInt(fac), mon);
      }
      reference.emplace_back(mon);
    }
    Node ref = d_nodeManager->mkNode(Kind::PLUS, std::move(reference));
    EXPECT_EQ(ref, prod);
  }
}

}  // namespace test
}  // namespace cvc5
