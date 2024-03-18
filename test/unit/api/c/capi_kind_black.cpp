/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Cvc5Kind enum of the  C API.
 */

#include <cvc5/c/cvc5.h>

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiKind : public ::testing::Test
{
};

TEST_F(TestCApiKind, kind_to_string)
{
  ASSERT_DEATH(cvc5_kind_to_string(static_cast<Cvc5Kind>(-5)),
               "invalid term kind");

  for (int32_t k = static_cast<int32_t>(CVC5_KIND_INTERNAL_KIND);
       k < static_cast<int32_t>(CVC5_KIND_LAST_KIND);
       ++k)
  {
    std::string kindstr = cvc5_kind_to_string(static_cast<Cvc5Kind>(k));
    if (k == static_cast<int32_t>(CVC5_KIND_INTERNAL_KIND))
    {
      ASSERT_EQ(kindstr, "CVC5_KIND_INTERNAL_KIND");
    }
    else if (k == static_cast<int32_t>(CVC5_KIND_UNDEFINED_KIND))
    {
      ASSERT_EQ(kindstr, "CVC5_KIND_UNDEFINED_KIND");
    }
    else
    {
      // If this assertion fails, s_kinds in cvc5.cpp is missing kind k.
      ASSERT_NE(kindstr, "CVC5_KIND_UNDEFINED_KIND");
      ASSERT_NE(kindstr, "CVC5_KIND_INTERNAL_KIND");
    }
  }
}
}  // namespace cvc5::internal::test
