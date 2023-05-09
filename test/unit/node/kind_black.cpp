/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::Kind.
 */

#include <iostream>
#include <sstream>
#include <string>

#include "expr/kind.h"
#include "test.h"

namespace cvc5::internal {

using namespace kind;

namespace test {

class TestNodeBlackKind : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_undefined = UNDEFINED_KIND;
    d_null = NULL_EXPR;
    d_last = LAST_KIND;
    d_beyond = ((int32_t)LAST_KIND) + 1;
    d_unknown = (Kind)d_beyond;
  }

  bool string_is_as_expected(Kind k, const char* s)
  {
    std::stringstream act;
    std::stringstream exp;
    act << k;
    exp << s;
    return act.str() == exp.str();
  }

  Kind d_undefined;
  Kind d_unknown;
  Kind d_null;
  Kind d_last;
  int32_t d_beyond;
};

TEST_F(TestNodeBlackKind, equality)
{
  ASSERT_EQ(d_undefined, UNDEFINED_KIND);
  ASSERT_EQ(d_last, LAST_KIND);
}

TEST_F(TestNodeBlackKind, order)
{
  ASSERT_LT((int32_t)d_undefined, (int32_t)d_null);
  ASSERT_LT((int32_t)d_null, (int32_t)d_last);
  ASSERT_LT((int32_t)d_undefined, (int32_t)d_last);
  ASSERT_LT((int32_t)d_last, (int32_t)d_unknown);
}

TEST_F(TestNodeBlackKind, output)
{
  ASSERT_TRUE(string_is_as_expected(d_undefined, "UNDEFINED_KIND"));
  ASSERT_TRUE(string_is_as_expected(d_null, "NULL"));
  ASSERT_TRUE(string_is_as_expected(d_last, "LAST_KIND"));
}

TEST_F(TestNodeBlackKind, output_concat)
{
  std::stringstream act, exp;
  act << d_undefined << d_null << d_last << d_unknown;
  exp << "UNDEFINED_KIND"
      << "NULL"
      << "LAST_KIND"
      << "?";
  ASSERT_EQ(act.str(), exp.str());
}
}  // namespace test
}  // namespace cvc5::internal
