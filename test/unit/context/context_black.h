/*********************                                           -*- C++ -*-  */
/** context_black.h
 ** Original author: dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>

//Used in some of the tests
#include <vector>
#include <iostream>
#include "context/context.h"

using namespace std;
using namespace CVC4::context;

class ContextBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context();
  }

  void testIntCDO() {
    // Test that push/pop maintains the original value
    CDO<int> a1(d_context);
    a1 = 5;
    TS_ASSERT(d_context->getLevel() == 0);
    d_context->push();
    a1 = 10;
    TS_ASSERT(d_context->getLevel() == 1);
    TS_ASSERT(a1 == 10);
    d_context->pop();
    TS_ASSERT(d_context->getLevel() == 0);
    TS_ASSERT(a1 == 5);
  }

  void testContextPushPop() {
    // Test what happens when the context is popped below 0
    // the interface doesn't declare any exceptions
    d_context->push();
    d_context->pop();
    d_context->pop();
    d_context->pop();
  }

  void tearDown() {
    delete d_context;
  }
};
