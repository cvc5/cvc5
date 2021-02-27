/*********************                                                        */
/*! \file assert_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::Configuration.
 **
 ** White box testing of CVC4::Configuration.
 **/

#include <cstring>
#include <string>

#include "base/check.h"
#include "test.h"

namespace CVC4 {
namespace test {

class TestUtilWhite : public TestInternal
{
};

TEST_F(TestUtilWhite, Assert)
{
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(Assert(false), "false");
#else
  ASSERT_NO_THROW(Assert(false));
#endif
  ASSERT_DEATH(AlwaysAssert(false), "false");
  ASSERT_NO_FATAL_FAILURE(Assert(true));
  ASSERT_NO_FATAL_FAILURE(AlwaysAssert(true));
}

TEST_F(TestUtilWhite, AssertArgument)
{
#ifdef CVC4_ASSERTIONS
  ASSERT_THROW(AssertArgument(false, "x"), AssertArgumentException);
#else
  ASSERT_NO_THROW(AssertArgument(false, "x"));
#endif
  ASSERT_THROW(AlwaysAssertArgument(false, "x"), AssertArgumentException);
  ASSERT_NO_THROW(AssertArgument(true, "x"));
  ASSERT_NO_THROW(AssertArgument(true, "x"));
}

TEST_F(TestUtilWhite, Unreachable)
{
  ASSERT_DEATH(Unreachable(), "Unreachable code reached");
  ASSERT_DEATH(Unreachable() << "hello", "Unreachable code reachedhello");
  ASSERT_DEATH(Unreachable() << "hello "
                             << "world",
               "Unreachable code reachedhello world");
}

TEST_F(TestUtilWhite, Unhandled)
{
  ASSERT_DEATH(Unhandled(), "Unhandled case encountered");
  ASSERT_DEATH(Unhandled() << 5, "Unhandled case encountered5");
  ASSERT_DEATH(Unhandled() << "foo", "Unhandled case encounteredfoo");
  ASSERT_DEATH(Unhandled() << "foo "
                           << "bar"
                           << " baz",
               "Unhandled case encounteredfoo bar baz");
}

TEST_F(TestUtilWhite, Unimplemented)
{
  ASSERT_DEATH(Unimplemented(), "Unimplemented code encountered");
}

TEST_F(TestUtilWhite, IllegalArgument)
{
  ASSERT_THROW(IllegalArgument("x"), IllegalArgumentException);
}

TEST_F(TestUtilWhite, CheckArgument)
{
  ASSERT_THROW(CheckArgument(false, "x"), IllegalArgumentException);
}
}  // namespace test
}  // namespace CVC4
