/*********************                                                        */
/** assert_white.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** White box testing of CVC4::Configuration.
 **/

#include <cxxtest/TestSuite.h>

#include "util/Assert.h"

using namespace CVC4;
using namespace std;

class AssertWhite : public CxxTest::TestSuite {
public:

  void testAssert() {
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( Assert(false), AssertionException );
    TS_ASSERT_THROWS( AssertArgument(false, "x"), IllegalArgumentException );
#else /* CVC4_ASSERTIONS */
    TS_ASSERT_THROWS_NOTHING( Assert(false) );
    TS_ASSERT_THROWS_NOTHING( AssertArgument(false, "x") );
#endif /* CVC4_ASSERTIONS */

    TS_ASSERT_THROWS_NOTHING( Assert(true) );
    TS_ASSERT_THROWS( AlwaysAssert(false), AssertionException );
    TS_ASSERT_THROWS( Unreachable(), UnreachableCodeException );
    TS_ASSERT_THROWS( Unhandled(), UnhandledCaseException );
    TS_ASSERT_THROWS( Unimplemented(), UnimplementedOperationException );
    TS_ASSERT_THROWS( IllegalArgument("x"), IllegalArgumentException );
    TS_ASSERT_THROWS( CheckArgument(false, "x"), IllegalArgumentException );
    TS_ASSERT_THROWS( AlwaysAssertArgument(false, "x"), IllegalArgumentException );
    TS_ASSERT_THROWS_NOTHING( AssertArgument(true, "x") );
    TS_ASSERT_THROWS_NOTHING( AssertArgument(true, "x") );
  }

};
