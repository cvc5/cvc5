/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SortKind enum of the  C++ API.
 */

#include <cvc5/cvc5.h>

#include <algorithm>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal {

namespace test {

class TestApiSortKind : public ::testing::Test
{
};

TEST_F(TestApiSortKind, sortKindToString)
{
  std::stringstream ss;
  for (int32_t k = static_cast<int32_t>(SortKind::INTERNAL_SORT_KIND);
       k < static_cast<int32_t>(SortKind::LAST_SORT_KIND);
       ++k)
  {
    SortKind sk = static_cast<SortKind>(k);
    ss << sk << std::endl;
    auto kindstr = std::to_string(sk);
    if (k == static_cast<int32_t>(SortKind::INTERNAL_SORT_KIND))
    {
      ASSERT_EQ(kindstr, "INTERNAL_SORT_KIND");
    }
    else if (k == static_cast<int32_t>(SortKind::UNDEFINED_SORT_KIND))
    {
      ASSERT_EQ(kindstr, "UNDEFINED_SORT_KIND");
    }
    else
    {
      // If this assertion fails, s_kinds in cvc5.cpp is missing kind k.
      ASSERT_NE(kindstr, "UNDEFINED_SORT_KIND");
      ASSERT_NE(kindstr, "INTERNAL_SORT_KIND");
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
