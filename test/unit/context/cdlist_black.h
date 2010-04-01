/*********************                                                        */
/** cdlist_black.h
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
 ** Black box testing of CVC4::context::CDList<>.
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <iostream>
#include "context/context.h"
#include "context/cdlist.h"

using namespace std;
using namespace CVC4::context;

class CDListBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context();
  }

  // test at different sizes.  this triggers grow() behavior differently.
  // grow() was completely broken in revision 256
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
