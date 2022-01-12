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
}

}  // namespace test
}  // namespace cvc5
