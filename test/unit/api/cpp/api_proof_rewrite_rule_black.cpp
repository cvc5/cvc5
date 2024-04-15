/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the ProofRewriteRule enum of the C++ API.
 */

#include <cvc5/cvc5_proof_rewrite_rule.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiProofRewriteRule : public ::testing::Test
{
};

TEST_F(TestApiProofRewriteRule, ProofRewriteRuleToString)
{
  for (int32_t i = static_cast<int32_t>(ProofRewriteRule::NONE);
       i <= static_cast<int32_t>(ProofRewriteRule::DISTINCT_BINARY_ELIM);
       ++i)
  {
    auto rulestr = std::to_string(static_cast<ProofRewriteRule>(i));
    // If this assertion fails, the switch in enum_to_string.cpp is missing
    // id i.
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
