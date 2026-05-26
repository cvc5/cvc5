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
  NodeManager* nm = d_nodeManager.get();
  arith::nl::Pow2ProofRuleChecker checker(nm);

  // Create an integer variable
  Node x = nm->mkVar("x", nm->integerType());
  // Empty for pow2 proof rules
  std::vector<Node> children;
  // Simple argument
  std::vector<Node> args = {x};
  
  // trivial implementation returns null
  Node result = checker.checkInternal(ProofRule::ARITH_POW2_INIT_REFINE, children, args);
  ASSERT_TRUE(result.isNull()); 
}

}  // namespace test
}  // namespace cvc5::internal
