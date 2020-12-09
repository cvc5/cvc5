/*********************                                                        */
/*! \file kind_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Kind.
 **
 ** Black box testing of CVC4::Kind.
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "expr/kind.h"
#include "test_expr.h"

namespace CVC4 {

using namespace kind;

namespace test {

class TestExprBlackKind : public TestExprBlack
{
 protected:
  void SetUp() override
  {
    undefined = UNDEFINED_KIND;
    null = NULL_EXPR;
    last = LAST_KIND;
    beyond = ((int32_t)LAST_KIND) + 1;
    unknown = (Kind)beyond;
  }

  bool string_is_as_expected(Kind k, const char* s)
  {
    std::stringstream act;
    std::stringstream exp;
    act << k;
    exp << s;
    return act.str() == exp.str();
  }

  Kind undefined;
  Kind unknown;
  Kind null;
  Kind last;
  int32_t beyond;
};

TEST_F(TestExprBlackKind, equality)
{
  EXPECT_EQ(undefined, UNDEFINED_KIND);
  EXPECT_EQ(last, LAST_KIND);
}

TEST_F(TestExprBlackKind, order)
{
  EXPECT_LT((int32_t)undefined, (int32_t)null);
  EXPECT_LT((int32_t)null, (int32_t)last);
  EXPECT_LT((int32_t)undefined, (int32_t)last);
  EXPECT_LT((int32_t)last, (int32_t)unknown);
}

TEST_F(TestExprBlackKind, output)
{
  ASSERT_TRUE(string_is_as_expected(undefined, "UNDEFINED_KIND"));
  ASSERT_TRUE(string_is_as_expected(null, "NULL"));
  ASSERT_TRUE(string_is_as_expected(last, "LAST_KIND"));
}

TEST_F(TestExprBlackKind, output_concat)
{
  std::stringstream act, exp;
  act << undefined << null << last << unknown;
  exp << "UNDEFINED_KIND"
      << "NULL"
      << "LAST_KIND"
      << "?";
  EXPECT_EQ(act.str(), exp.str());
}
}  // namespace test
}  // namespace CVC4
