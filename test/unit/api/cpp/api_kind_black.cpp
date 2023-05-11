/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Kind enum of the  C++ API.
 */

#include <cvc5/cvc5.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiKind : public ::testing::Test
{
};

TEST_F(TestApiKind, kindToString)
{
  for (int32_t k = INTERNAL_KIND; k < LAST_KIND; ++k)
  {
    auto kindstr = kindToString(static_cast<Kind>(k));
    if (k == INTERNAL_KIND)
    {
      ASSERT_EQ(kindstr, "INTERNAL_KIND");
    }
    else if (k == UNDEFINED_KIND)
    {
      ASSERT_EQ(kindstr, "UNDEFINED_KIND");
    }
    else
    {
      // If this assertion fails, s_kinds in cvc5.cpp is missing kind k.
      ASSERT_NE(kindstr, "UNDEFINED_KIND");
      ASSERT_NE(kindstr, "INTERNAL_KIND");
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
