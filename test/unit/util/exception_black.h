/*********************                                                        */
/*! \file exception_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Exception.
 **
 ** Black box testing of CVC4::Exception.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <sstream>

#include "base/exception.h"

using namespace CVC4;
using namespace std;

class ExceptionBlack : public CxxTest::TestSuite {
 public:
  void setUp() override {}

  void tearDown() override {}

  // CVC4::Exception is a simple class, just test it all at once.
  void testExceptions()
  {
    Exception e1;
    Exception e2(string("foo!"));
    Exception e3("bar!");

    TS_ASSERT_EQUALS(e1.toString(), string("Unknown exception"));
    TS_ASSERT_EQUALS(e2.toString(), string("foo!"));
    TS_ASSERT_EQUALS(e3.toString(), string("bar!"));

    e1.setMessage("blah");
    e2.setMessage("another");
    e3.setMessage("three of 'em!");

    stringstream s1, s2, s3;
    s1 << e1;
    s2 << e2;
    s3 << e3;

    TS_ASSERT_EQUALS(s1.str(), string("blah"));
    TS_ASSERT_EQUALS(s2.str(), string("another"));
    TS_ASSERT_EQUALS(s3.str(), string("three of 'em!"));
  }
};
