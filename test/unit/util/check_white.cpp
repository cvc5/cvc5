/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of check utilities.
 */

#include <cstring>
#include <string>

#include "base/check.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

class TestUtilWhiteCheck : public TestInternal
{
 protected:
  static constexpr uint32_t K_ONE = 1;

  // This test just checks that this statement compiles.
  std::string terminalCvc5Fatal() const
  {
    CVC5_FATAL() << "This is a test that confirms that CVC5_FATAL can be a "
                    "terminal statement in a function that has a non-void "
                    "return type.";
  }
};

TEST_F(TestUtilWhiteCheck, check)
{
  AlwaysAssert(K_ONE >= 0) << K_ONE << " must be positive";
}

TEST_F(TestUtilWhiteCheck, dcheck)
{
  Assert(K_ONE == 1) << "always passes";
#ifndef CVC5_ASSERTIONS
  Assert(false) << "Will not be compiled in when CVC5_ASSERTIONS off.";
#endif
}

TEST_F(TestUtilWhiteCheck, pointer_type_can_be_condition)
{
  const uint32_t* one_pointer = &K_ONE;
  Assert(one_pointer);
  AlwaysAssert(one_pointer);
}

TEST_F(TestUtilWhiteCheck, expect_abort)
{
  ASSERT_DEATH(Assert(false), "false");
  ASSERT_DEATH(AlwaysAssert(false), "false");
}
}  // namespace test
}  // namespace cvc5::internal
