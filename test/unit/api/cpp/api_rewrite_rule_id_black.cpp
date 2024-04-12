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
 * Black box testing of the RewriteRuleId enum of the C++ API.
 */

#include <cvc5/cvc5_rewrite_rule_id.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiRewriteRuleId : public ::testing::Test
{
};

TEST_F(TestApiRewriteRuleId, RewriteRuleIdToString)
{
  for (int32_t i = static_cast<int32_t>(RewriteRuleId::NONE);
       i <= static_cast<int32_t>(RewriteRuleId::DISTINCT_BINARY_ELIM);
       ++i)
  {
    auto rulestr = std::to_string(static_cast<RewriteRuleId>(i));
    // If this assertion fails, the switch in enum_to_string.cpp is missing
    // id i.
    ASSERT_NE(rulestr, "?");
  }
}

TEST_F(TestApiRewriteRuleId, RewriteRuleIdHash)
{
  ASSERT_EQ(std::hash<cvc5::RewriteRuleId>()(RewriteRuleId::NONE),
            static_cast<size_t>(RewriteRuleId::NONE));
}

}  // namespace test
}  // namespace cvc5::internal
