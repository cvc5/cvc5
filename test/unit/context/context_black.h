/*********************                                                        */
/** context_black.h
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
//    d_context->pop();
//    d_context->pop();
  }

  // test at different sizes.  this triggers grow() behavior differently.
  // grow() is completely broken in revision 256; fix forthcoming by Tim
  void testCDList10() { listTest(10); }
  void testCDList15() { listTest(15); }
  void testCDList20() { listTest(20); }
  void testCDList35() { listTest(35); }
  void testCDList50() { listTest(50); }
  void testCDList99() { listTest(99); }

  void listTest(int N) {
    CDList<int> list(d_context);

    TS_ASSERT(list.empty());
    for(int i = 0; i < N; ++i) {
      TS_ASSERT(list.size() == i);
      list.push_back(i);
      TS_ASSERT(!list.empty());
      TS_ASSERT(list.back() == i);
      int i2 = 0;
      for(CDList<int>::const_iterator j = list.begin();
          j != list.end();
          ++j) {
        TS_ASSERT(*j == i2++);
      }
    }
    TS_ASSERT(list.size() == N);

    for(int i = 0; i < N; ++i) {
      TS_ASSERT(list[i] == i);
    }
  }

  void tearDown() {
    delete d_context;
  }
};
