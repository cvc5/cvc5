/*********************                                                        */
/*! \file assert_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Morgan Deters, Andres Noetzli
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

#include <cxxtest/TestSuite.h>

#include <string>
#include <cstring>

#include "base/check.h"
#include "test_utils.h"

using namespace CVC4;
using namespace std;

class AssertWhite : public CxxTest::TestSuite {
public:
 void testAssert()
 {
#ifdef CVC4_ASSERTIONS
   TS_UTILS_EXPECT_ABORT(Assert(false));
   TS_ASSERT_THROWS(AssertArgument(false, "x"), AssertArgumentException&);
#else /* CVC4_ASSERTIONS */
   TS_ASSERT_THROWS_NOTHING(Assert(false));
   TS_ASSERT_THROWS_NOTHING(AssertArgument(false, "x"));
#endif /* CVC4_ASSERTIONS */

   TS_ASSERT_THROWS_NOTHING(Assert(true));
   TS_UTILS_EXPECT_ABORT(AlwaysAssert(false));
   TS_UTILS_EXPECT_ABORT(Unreachable());
   TS_UTILS_EXPECT_ABORT(Unhandled());
   TS_UTILS_EXPECT_ABORT(Unimplemented());
   TS_ASSERT_THROWS(IllegalArgument("x"), IllegalArgumentException&);
   TS_ASSERT_THROWS(CheckArgument(false, "x"), IllegalArgumentException&);
   TS_ASSERT_THROWS(AlwaysAssertArgument(false, "x"), AssertArgumentException&);
   TS_ASSERT_THROWS_NOTHING(AssertArgument(true, "x"));
   TS_ASSERT_THROWS_NOTHING(AssertArgument(true, "x"));
 }

  void testUnreachable() {
    TS_UTILS_EXPECT_ABORT(Unreachable());
    TS_UTILS_EXPECT_ABORT(Unreachable() << "hello");
    TS_UTILS_EXPECT_ABORT(Unreachable() << "hello "
                                        << "world");

    int x = 5;
    TS_UTILS_EXPECT_ABORT(Unhandled());
    TS_UTILS_EXPECT_ABORT(Unhandled() << x);
    TS_UTILS_EXPECT_ABORT(Unhandled() << "foo");
    TS_UTILS_EXPECT_ABORT(Unhandled() << "foo "
                                      << "bar"
                                      << " baz");
  }

};
