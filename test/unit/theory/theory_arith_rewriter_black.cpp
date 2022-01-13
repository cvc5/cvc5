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
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 3);
    Node n = d_nodeManager->mkRealAlgebraicNumber(sqrt2);
    n = d_nodeManager->mkNode(Kind::MINUS, n, n);
    n = d_slvEngine->getRewriter()->rewrite(n);
    EXPECT_EQ(n.getKind(), Kind::CONST_RATIONAL);
    EXPECT_EQ(n.getConst<Rational>(), Rational(0));
  }
}

}  // namespace test
}  // namespace cvc5
