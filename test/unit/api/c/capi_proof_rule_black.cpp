/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of proof-rule-related functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackProofRule : public ::testing::Test
{
};
class TestCApiProofRewriteRule : public ::testing::Test
{
};

TEST_F(TestCApiBlackProofRule, proofRuleToString)
{
  for (int32_t r = static_cast<int32_t>(CVC5_PROOF_RULE_ASSUME);
       r <= static_cast<int32_t>(CVC5_PROOF_RULE_UNKNOWN);
       ++r)
  {
    Cvc5ProofRule rule = static_cast<Cvc5ProofRule>(r);
    // If this assertion fails, the switch is missing rule r.
    ASSERT_NE(cvc5_proof_rule_to_string(rule), std::string("?"));
  }
}

TEST_F(TestCApiBlackProofRule, hash)
{
  ASSERT_EQ(cvc5_proof_rule_hash(CVC5_PROOF_RULE_UNKNOWN),
            static_cast<size_t>(CVC5_PROOF_RULE_UNKNOWN));
}

TEST_F(TestCApiProofRewriteRule, ProofRewriteRuleToString)
{
  for (int32_t r = static_cast<int32_t>(CVC5_PROOF_REWRITE_RULE_NONE);
       r <= static_cast<int32_t>(CVC5_PROOF_REWRITE_RULE_DISTINCT_BINARY_ELIM);
       ++r)
  {
    // If this assertion fails, the switch is missing rule r.
    Cvc5ProofRewriteRule rule = static_cast<Cvc5ProofRewriteRule>(r);
    ASSERT_NE(cvc5_proof_rewrite_rule_to_string(rule), std::string("?"));
  }
}

TEST_F(TestCApiProofRewriteRule, hash)
{
  ASSERT_EQ(cvc5_proof_rewrite_rule_hash(CVC5_PROOF_REWRITE_RULE_NONE),
            static_cast<size_t>(CVC5_PROOF_REWRITE_RULE_NONE));
}
}  // namespace cvc5::internal::test
