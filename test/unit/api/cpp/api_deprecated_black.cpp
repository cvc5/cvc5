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
 * These tests are purely for the purpose of covering deprecated API functions
 * for the nightly API coverage builds.
 */

#include <cvc5/cvc5.h>

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestApiDeprecated : public ::testing::Test
{
};

TEST_F(TestApiDeprecated, kindToString)
{
  for (int32_t k = static_cast<int32_t>(Kind::INTERNAL_KIND);
       k < static_cast<int32_t>(Kind::LAST_KIND);
       ++k)
  {
    ASSERT_EQ(kindToString(static_cast<Kind>(k)),
              std::to_string(static_cast<Kind>(k)));
  }
}

TEST_F(TestApiDeprecated, sortKindToString)
{
  for (int32_t k = static_cast<int32_t>(SortKind::INTERNAL_SORT_KIND);
       k < static_cast<int32_t>(SortKind::LAST_SORT_KIND);
       ++k)
  {
    ASSERT_EQ(sortKindToString(static_cast<SortKind>(k)),
              std::to_string(static_cast<SortKind>(k)));
  }
}

}  // namespace cvc5::internal::test
