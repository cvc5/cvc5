/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

#include "test_smt.h"
#include "theory/arith/nl/pow2_proof_checker.h"
#include "theory/arith/nl/pow2_solver.h"
#include "util/rational.h"

namespace cvc5::internal {

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
  }
};

TEST_F(TestTheoryWhiteArithPow2, pow2_proof_checker_basic)
{
  NodeManager* nm = d_nodeManager.get();
  arith::nl::Pow2ProofRuleChecker checker(nm);

  // Create an integer variable
  Node x = nm->mkVar("x", nm->integerType());
  // Empty for pow2 proof rules
  std::vector<Node> children;
  // Simple argument
  std::vector<Node> args = {x};

  Node result =
      checker.checkInternal(ProofRule::ARITH_POW2_INIT, children, args);

  Node zero = nm->mkConstInt(Rational(0));
  Node two = nm->mkConstInt(Rational(2));
  Node pt = nm->mkNode(Kind::POW2, x);
  Node nonneg = nm->mkNode(
      Kind::IMPLIES, nm->mkNode(Kind::GEQ, x, zero), nm->mkNode(Kind::GT, pt, zero));
  Node even = nm->mkNode(
      Kind::IMPLIES,
      nm->mkNode(Kind::DISTINCT, x, zero),
      nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::INTS_MODULUS, pt, two), zero));
  Node neg = nm->mkNode(
      Kind::IMPLIES, nm->mkNode(Kind::LT, x, zero), nm->mkNode(Kind::EQUAL, pt, zero));
  Node expected = nm->mkNode(Kind::AND, nonneg, even, neg);

  ASSERT_EQ(result, expected);
}

}  // namespace test
}  // namespace cvc5::internal
