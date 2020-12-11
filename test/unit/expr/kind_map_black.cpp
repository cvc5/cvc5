/*********************                                                        */
/*! \file kind_map_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::KindMap
 **
 ** Black box testing of CVC4::KindMap.
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "expr/kind_map.h"
#include "test_expr.h"

namespace CVC4 {

using namespace kind;

namespace test {

class TestExprBlackKindMap : public TestExprBlack
{
};

TEST_F(TestExprBlackKindMap, simple)
{
  KindMap map;
  ASSERT_FALSE(map.test(AND));
  map.set(AND);
  ASSERT_TRUE(map.test(AND));
  map.reset(AND);
  ASSERT_FALSE(map.test(AND));
#ifdef CVC4_ASSERTIONS
  ASSERT_THROW(map.set(LAST_KIND), AssertArgumentException);
#endif
}

}  // namespace test
}  // namespace CVC4
