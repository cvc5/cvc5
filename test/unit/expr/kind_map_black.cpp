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
  ASSERT_TRUE(map.isEmpty());
  map.set(AND);
  ASSERT_FALSE(map.isEmpty());
  KindMap map2 = map;
  ASSERT_FALSE(map2.isEmpty());
  EXPECT_EQ(map, map2);
  ASSERT_TRUE(map.tst(AND));
  ASSERT_TRUE(map2.tst(AND));
  ASSERT_FALSE(map.tst(OR));
  ASSERT_FALSE(map2.tst(OR));
  map2 = ~map2;
  ASSERT_TRUE(map2.tst(OR));
  ASSERT_FALSE(map2.tst(AND));
  EXPECT_NE(map, map2);
  EXPECT_NE(map.begin(), map.end());
  EXPECT_NE(map2.begin(), map2.end());
  map &= ~AND;
  ASSERT_TRUE(map.isEmpty());
  map2.clear();
  ASSERT_TRUE(map2.isEmpty());
  EXPECT_EQ(map2, map);
  EXPECT_EQ(map.begin(), map.end());
  EXPECT_EQ(map2.begin(), map2.end());
}

TEST_F(TestExprBlackKindMap, iteration)
{
  KindMap m = AND & OR;
  ASSERT_TRUE(m.isEmpty());
  for (KindMap::iterator i = m.begin(); i != m.end(); ++i)
  {
    ASSERT_TRUE(false) << "expected empty iterator range";
  }
  m = AND | OR;
  KindMap::iterator i = m.begin();
  EXPECT_NE(i, m.end());
  EXPECT_EQ(*i, AND);
  ++i;
  EXPECT_NE(i, m.end());
  EXPECT_EQ(*i, OR);
  ++i;
  EXPECT_EQ(i, m.end());

  m = ~m;
  unsigned k = 0;
  for (i = m.begin(); i != m.end(); ++i, ++k)
  {
    while (k == AND || k == OR)
    {
      ++k;
    }
    EXPECT_NE(Kind(k), UNDEFINED_KIND);
    EXPECT_NE(Kind(k), LAST_KIND);
    EXPECT_EQ(*i, Kind(k));
  }
}

TEST_F(TestExprBlackKindMap, construction)
{
  ASSERT_FALSE((AND & AND).isEmpty());
  ASSERT_TRUE((AND & ~AND).isEmpty());
  ASSERT_FALSE((AND & AND & AND).isEmpty());

  ASSERT_FALSE((AND | AND).isEmpty());
  ASSERT_FALSE((AND | ~AND).isEmpty());
  ASSERT_TRUE(((AND | AND) & ~AND).isEmpty());
  ASSERT_FALSE(((AND | OR) & ~AND).isEmpty());

  ASSERT_TRUE((AND ^ AND).isEmpty());
  ASSERT_FALSE((AND ^ OR).isEmpty());
  ASSERT_FALSE((AND ^ AND ^ AND).isEmpty());

#ifdef CVC4_ASSERTIONS
  ASSERT_THROW(~LAST_KIND, AssertArgumentException);
#endif
}

}  // namespace test
}  // namespace CVC4
