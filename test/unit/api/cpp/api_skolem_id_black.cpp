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
 * Black box testing of the SkolemFunId enum of the C++ API.
 */

#include <cvc5/cvc5_proof_rule.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiSkolemFunId : public ::testing::Test
{
};

TEST_F(TestApiSkolemFunId, proofRuleToString)
{
  for (int32_t r = static_cast<int32_t>(SkolemFunId::ASSUME);
       r < static_cast<int32_t>(SkolemFunId::UNKNOWN);
       ++r)
  {
    auto rulestr = toString(static_cast<SkolemFunId>(r));
    if (r == static_cast<int32_t>(SkolemFunId::UNKNOWN))
    {
      ASSERT_EQ(rulestr, "UNKNOWN");
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
