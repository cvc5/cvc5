/*********************                                                        */
/** context_black.h
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::context::Context.
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <iostream>
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "util/Assert.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

class ContextBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context;
  }

  void tearDown() {
    delete d_context;
  }

  void testContextPushPop() {
    // Test what happens when the context is popped below 0
    // the interface doesn't declare any exceptions
    d_context->push();
    d_context->pop();
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( d_context->pop(), AssertionException );
    TS_ASSERT_THROWS( d_context->pop(), AssertionException );
#endif /* CVC4_ASSERTIONS */
  }

  void testDtor() {
    // Destruction of ContextObj was broken in revision 324 (bug #45) when
    // at a higher context level with an intervening modification.
    // (The following caused a "pure virtual method called" error.)
    CDO<int> i(d_context);
    d_context->push();
    i = 5;
  }

  void testPreNotify() {
    struct MyContextNotifyObj : ContextNotifyObj {
      int nCalls;

      MyContextNotifyObj(Context* context, bool pre) :
        ContextNotifyObj(context, pre),
        nCalls(0) {
      }

      void notify() {
        ++nCalls;
      }
    } a(d_context, true), b(d_context, false);

    {
      MyContextNotifyObj c(d_context, true), d(d_context, false);

      TS_ASSERT_EQUALS(a.nCalls, 0);
      TS_ASSERT_EQUALS(b.nCalls, 0);
      TS_ASSERT_EQUALS(c.nCalls, 0);
      TS_ASSERT_EQUALS(d.nCalls, 0);

      d_context->push();
      d_context->push();

      TS_ASSERT_EQUALS(a.nCalls, 0);
      TS_ASSERT_EQUALS(b.nCalls, 0);
      TS_ASSERT_EQUALS(c.nCalls, 0);
      TS_ASSERT_EQUALS(d.nCalls, 0);

      d_context->pop();

      TS_ASSERT_EQUALS(a.nCalls, 1);
      TS_ASSERT_EQUALS(b.nCalls, 1);
      TS_ASSERT_EQUALS(c.nCalls, 1);
      TS_ASSERT_EQUALS(d.nCalls, 1);

      d_context->pop();

      TS_ASSERT_EQUALS(a.nCalls, 2);
      TS_ASSERT_EQUALS(b.nCalls, 2);
      TS_ASSERT_EQUALS(c.nCalls, 2);
      TS_ASSERT_EQUALS(d.nCalls, 2);
    }

    // we do this to get full code coverage of destruction paths
    delete d_context;

    d_context = NULL;
  }
};
