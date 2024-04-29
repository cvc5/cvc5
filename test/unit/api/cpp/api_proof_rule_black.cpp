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
 * Black box testing of the ProofRule enum of the C++ API.
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
       r <= static_cast<int32_t>(ProofRule::UNKNOWN);
       ++r)
  {
    ProofRule rule = static_cast<ProofRule>(r);
    auto rulestr = toString(rule);
    // If this assertion fails, the switch is missing rule r.
    ASSERT_NE(rulestr, "?");
  }
}

TEST_F(TestApiProofRule, ProofRuleHash)
{
  ASSERT_EQ(std::hash<cvc5::ProofRule>()(ProofRule::UNKNOWN),
            static_cast<size_t>(ProofRule::UNKNOWN));
}

class TestApiProofRewriteRule : public ::testing::Test
{
};

TEST_F(TestApiProofRewriteRule, ProofRewriteRuleToString)
{
  for (int32_t r = static_cast<int32_t>(ProofRewriteRule::NONE);
       r <= static_cast<int32_t>(ProofRewriteRule::DISTINCT_BINARY_ELIM);
       ++r)
  {
    auto rulestr = std::to_string(static_cast<ProofRewriteRule>(r));
    // If this assertion fails, the switch is missing rule r.
    ASSERT_NE(rulestr, "?");
  }
}

TEST_F(TestApiProofRewriteRule, ProofRewriteRuleHash)
{
  ASSERT_EQ(std::hash<cvc5::ProofRewriteRule>()(ProofRewriteRule::NONE),
            static_cast<size_t>(ProofRewriteRule::NONE));
}

}  // namespace test
}  // namespace cvc5::internal
