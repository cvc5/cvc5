/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Kind enum of the  C++ API.
 */

#include <cvc5/cvc5_proof_rule.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiProofRule : public ::testing::Test
{
};

TEST_F(TestApiProofRule, proofRuleToString)
{
  for (int32_t r = static_cast<int32_t>(ProofRule::ASSUME);
       r < static_cast<int32_t>(ProofRule::UNKNOWN);
       ++r)
  {
    auto rulestr = toString(static_cast<ProofRule>(r));
    if (r == static_cast<int32_t>(ProofRule::UNKNOWN))
    {
      ASSERT_EQ(rulestr, "UNKNONW");
    }
    else
    {
      // If this assertion fails, the switch in cvc5_proof_rule.cpp is missing
      // rule r.
      ASSERT_NE(rulestr, "UNKNOWN");
      ASSERT_NE(rulestr, "?");
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
