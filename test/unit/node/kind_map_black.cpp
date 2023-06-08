/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::KindMap.
 */

#include <iostream>
#include <sstream>
#include <string>

#include "expr/kind_map.h"
#include "test.h"

namespace cvc5::internal {

using namespace internal;
using namespace internal::kind;

namespace test {

class TestNodeBlackKindMap : public TestInternal
{
};

TEST_F(TestNodeBlackKindMap, simple)
{
  KindMap map;
  ASSERT_FALSE(map.test(AND));
  map.set(AND);
  ASSERT_TRUE(map.test(AND));
  map.reset(AND);
  ASSERT_FALSE(map.test(AND));
#ifdef CVC5_ASSERTIONS
  ASSERT_THROW(map.set(LAST_KIND), AssertArgumentException);
#endif
}

}  // namespace test
}  // namespace cvc5::internal
