/*********************                                                        */
/*! \file assert_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Paul Meng, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

#include "base/cvc4_assert.h"

using namespace CVC4;
using namespace std;

class AssertWhite : public CxxTest::TestSuite {
public:

  void testAssert() {
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( Assert(false), AssertionException );
    TS_ASSERT_THROWS( AssertArgument(false, "x"), AssertArgumentException );
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
    TS_ASSERT_THROWS( AlwaysAssertArgument(false, "x"),
                      AssertArgumentException );
    TS_ASSERT_THROWS_NOTHING( AssertArgument(true, "x") );
    TS_ASSERT_THROWS_NOTHING( AssertArgument(true, "x") );
  }

  void testReallyLongAssert() {
    string msg(1034, 'x');
    try {
      AlwaysAssert(false, msg.c_str());
      TS_FAIL("Should have thrown an exception !");
    } catch(AssertionException& e) {
      // we don't want to match on the entire string, because it may
      // have an absolute path to the unit test binary, line number
      // info, etc.
      std::string s = e.toString();
      const char* theString = s.c_str();
      const char* firstPart =
        "Assertion failure\nvoid AssertWhite::testReallyLongAssert()\n";
      string lastPartStr = "\n\n  false\n" + msg;
      const char* lastPart = lastPartStr.c_str();
      TS_ASSERT(strncmp(theString, firstPart, strlen(firstPart)) == 0);
      TS_ASSERT(strncmp(theString + strlen(theString) - strlen(lastPart),
                        lastPart, strlen(lastPart)) == 0);
    } catch(...) {
      TS_FAIL("Threw the wrong kind of exception !");
    }

    // Now test an assert with a format that drives it over the 512
    // byte initial buffer.  This was a bug in r1441, see bug:
    // https://github.com/CVC4/CVC4/issues/465
    string fmt = string(200, 'x') + " %s " + string(200, 'x');
    string arg(200, 'y');
    try {
      AlwaysAssert(false, fmt.c_str(), arg.c_str());
      TS_FAIL("Should have thrown an exception !");
    } catch(AssertionException& e) {
      // we don't want to match on the entire string, because it may
      // have an absolute path to the unit test binary, line number
      // info, etc.
      std::string s = e.toString();
      const char* theString = s.c_str();
      const char* firstPart =
        "Assertion failure\nvoid AssertWhite::testReallyLongAssert()\n";
      string lastPartStr = "\n\n  false\n" + string(200, 'x') + " " +
        string(200, 'y') + " " + string(200, 'x');
      const char* lastPart = lastPartStr.c_str();
      TS_ASSERT(strncmp(theString, firstPart, strlen(firstPart)) == 0);
      TS_ASSERT(strncmp(theString + strlen(theString) - strlen(lastPart),
                        lastPart, strlen(lastPart)) == 0);
    } catch(...) {
      TS_FAIL("Threw the wrong kind of exception !");
    }
  }

  void testUnreachable() {
    TS_ASSERT_THROWS( Unreachable(), UnreachableCodeException );
    TS_ASSERT_THROWS( Unreachable("hello"), UnreachableCodeException );
    TS_ASSERT_THROWS( Unreachable("hello %s", "world"), UnreachableCodeException );

    int x = 5;
    TS_ASSERT_THROWS( Unhandled(), UnhandledCaseException );
    TS_ASSERT_THROWS( Unhandled(x), UnhandledCaseException );
    TS_ASSERT_THROWS( Unhandled("foo"), UnhandledCaseException );
    TS_ASSERT_THROWS( Unhandled("foo %s baz", "bar"), UnhandledCaseException );
  }

};
