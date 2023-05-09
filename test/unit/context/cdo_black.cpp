/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Dejan Jovanovic, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::context::CDO<>.
 */

#include <iostream>
#include <vector>

#include "base/check.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "test_context.h"

namespace cvc5::internal {

using namespace context;

namespace test {

class TestContextBlackCDO : public TestContext
{
};

TEST_F(TestContextBlackCDO, cdo)
{
  // Test that push/pop maintains the original value
  CDO<int> a1(d_context.get());
  a1 = 5;
  ASSERT_EQ(d_context->getLevel(), 0);
  d_context->push();
  a1 = 10;
  ASSERT_EQ(d_context->getLevel(), 1);
  ASSERT_EQ(a1, 10);
  d_context->pop();
  ASSERT_EQ(d_context->getLevel(), 0);
  ASSERT_EQ(a1, 5);
}

}  // namespace test
}  // namespace cvc5::internal
