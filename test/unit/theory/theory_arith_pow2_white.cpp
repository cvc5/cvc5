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
#include "theory/arith/nl/pow2_solver.h"
#include "theory/arith/nl/pow2_proof_checker.h"
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
  // Test that the Pow2ProofRuleChecker can be instantiated and basic methods work
  NodeManager* nm = d_nodeManager;
  arith::nl::Pow2ProofRuleChecker checker(nm);

  // Create a simple integer term for testing
  Node x = nm->mkVar("x", nm->integerType());
  std::vector<Node> children;  // Empty for pow2 proof rules
  std::vector<Node> args = {x}; // Simple argument

  // Test that checkInternal returns null for our stub implementation
  Node result = checker.checkInternal(ProofRule::ARITH_POW2_INIT_REFINE, children, args);
  ASSERT_TRUE(result.isNull()) << "Expected null result from stub implementation";

  // Test another proof rule
  Node y = nm->mkVar("y", nm->integerType());
  std::vector<Node> args2 = {x, y};
  Node result2 = checker.checkInternal(ProofRule::ARITH_POW2_MONOTONE_REFINE, children, args2);
  ASSERT_TRUE(result2.isNull()) << "Expected null result from stub implementation";
}

}  // namespace test
}  // namespace cvc5::internal
