/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for pow2 operator.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "smt/logic_exception.h"
#include "test_smt.h"
#include "theory/arith/nl/pow2_solver.h"
#include "util/rational.h"

namespace cvc5 {

using namespace kind;
using namespace theory;

namespace test {

class TestTheoryWhiteArithPow2 : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("produce-models", "true");
    d_slvEngine->finishInit();
    d_true = d_nodeManager->mkConst<bool>(true);
    d_one = d_nodeManager->mkConst<Rational>(CONST_RATIONAL, Rational(1));
  }
  Node d_true;
  Node d_one;
};

TEST_F(TestTheoryWhiteArithPow2, largeConst)
{
  Node t203 = d_nodeManager->mkConst<Rational>(
      CONST_RATIONAL, Rational("6135470354240554220207"));
  Node two = d_nodeManager->mkConst<Rational>(CONST_RATIONAL, Rational("2"));
  Node t262 = d_nodeManager->mkNode(POW, two, t203);
  ASSERT_THROW(d_slvEngine->simplify(t262), LogicException);
}

}  // namespace test
}  // namespace cvc5
