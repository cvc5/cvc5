/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SkolemId enum of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackSkolemId : public ::testing::Test
{
};

TEST_F(TestCApiBlackSkolemId, to_string)
{
  for (int32_t i = static_cast<int32_t>(CVC5_SKOLEM_ID_INTERNAL);
       i <= static_cast<int32_t>(CVC5_SKOLEM_ID_NONE);
       ++i)
  {
    auto rulestr = cvc5_skolem_id_to_string(static_cast<Cvc5SkolemId>(i));
    // If this assertion fails, the switch in enum_to_string.cpp is missing
    // id i.
    ASSERT_NE(rulestr, "?");
  }
}

TEST_F(TestCApiBlackSkolemId, hash)
{
  ASSERT_EQ(cvc5_skolem_id_hash(CVC5_SKOLEM_ID_PURIFY),
            cvc5_skolem_id_hash(CVC5_SKOLEM_ID_PURIFY));
  ASSERT_NE(cvc5_skolem_id_hash(CVC5_SKOLEM_ID_INTERNAL),
            cvc5_skolem_id_hash(CVC5_SKOLEM_ID_PURIFY));
}
}  // namespace cvc5::internal::test
