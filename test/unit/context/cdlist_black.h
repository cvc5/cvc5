/*********************                                                        */
/*! \file cdlist_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::CDList<>.
 **
 ** Black box testing of CVC4::context::CDList<>.
 **/

#include <cxxtest/TestSuite.h>

#include <limits.h>
#include <iostream>
#include <vector>

#include "base/exception.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "memory.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4;

struct DtorSensitiveObject {
  bool& d_dtorCalled;
  DtorSensitiveObject(bool& dtorCalled) : d_dtorCalled(dtorCalled) {}
  ~DtorSensitiveObject() { d_dtorCalled = true; }
};

class CDListBlack : public CxxTest::TestSuite {
 private:
  Context* d_context;

 public:
  void setUp() override { d_context = new Context(); }

  void tearDown() override { delete d_context; }

  // test at different sizes.  this triggers grow() behavior differently.
  // grow() was completely broken in revision 256
  void testCDList10() { listTest(10); }
  void testCDList15() { listTest(15); }
  void testCDList20() { listTest(20); }
  void testCDList35() { listTest(35); }
  void testCDList50() { listTest(50); }
  void testCDList99() { listTest(99); }

  void listTest(int N) {
    listTest(N, true);
    listTest(N, false);
  }

  void listTest(int N, bool callDestructor) {
    CDList<int> list(d_context, callDestructor);

    TS_ASSERT(list.empty());
    for (int i = 0; i < N; ++i) {
      TS_ASSERT_EQUALS(list.size(), unsigned(i));
      list.push_back(i);
      TS_ASSERT(!list.empty());
      TS_ASSERT_EQUALS(list.back(), i);
      int i2 = 0;
      for (CDList<int>::const_iterator j = list.begin(); j != list.end(); ++j) {
        TS_ASSERT_EQUALS(*j, i2++);
      }
    }
    TS_ASSERT_EQUALS(list.size(), unsigned(N));

    for (int i = 0; i < N; ++i) {
      TS_ASSERT_EQUALS(list[i], i);
    }
  }

  void testDtorCalled() {
    bool shouldRemainFalse = false;
    bool shouldFlipToTrue = false;
    bool alsoFlipToTrue = false;
    bool shouldAlsoRemainFalse = false;
    bool aThirdFalse = false;

    CDList<DtorSensitiveObject> listT(d_context, true);
    CDList<DtorSensitiveObject> listF(d_context, false);

    DtorSensitiveObject shouldRemainFalseDSO(shouldRemainFalse);
    DtorSensitiveObject shouldFlipToTrueDSO(shouldFlipToTrue);
    DtorSensitiveObject alsoFlipToTrueDSO(alsoFlipToTrue);
    DtorSensitiveObject shouldAlsoRemainFalseDSO(shouldAlsoRemainFalse);
    DtorSensitiveObject aThirdFalseDSO(aThirdFalse);

    listT.push_back(shouldAlsoRemainFalseDSO);
    listF.push_back(shouldAlsoRemainFalseDSO);

    d_context->push();

    listT.push_back(shouldFlipToTrueDSO);
    listT.push_back(alsoFlipToTrueDSO);

    listF.push_back(shouldRemainFalseDSO);
    listF.push_back(shouldAlsoRemainFalseDSO);
    listF.push_back(aThirdFalseDSO);

    TS_ASSERT_EQUALS(shouldRemainFalse, false);
    TS_ASSERT_EQUALS(shouldFlipToTrue, false);
    TS_ASSERT_EQUALS(alsoFlipToTrue, false);
    TS_ASSERT_EQUALS(shouldAlsoRemainFalse, false);
    TS_ASSERT_EQUALS(aThirdFalse, false);

    d_context->pop();

    TS_ASSERT_EQUALS(shouldRemainFalse, false);
    TS_ASSERT_EQUALS(shouldFlipToTrue, true);
    TS_ASSERT_EQUALS(alsoFlipToTrue, true);
    TS_ASSERT_EQUALS(shouldAlsoRemainFalse, false);
    TS_ASSERT_EQUALS(aThirdFalse, false);
  }

  void testEmptyIterator() {
    CDList<int>* list = new (true) CDList<int>(d_context);
    TS_ASSERT_EQUALS(list->begin(), list->end());
    list->deleteSelf();
  }

  void testOutOfMemory() {
#ifdef CVC4_MEMORY_LIMITING_DISABLED

    test::WarnWithLimitedMemoryDisabledReason();

#else /* CVC4_MEMORY_LIMITING_DISABLED */

    CDList<unsigned> list(d_context);
    test::WithLimitedMemory wlm(1);

    TS_ASSERT_THROWS(
        {
          // We cap it at UINT_MAX, preferring to terminate with a
          // failure than run indefinitely.
          for (unsigned i = 0; i < UINT_MAX; ++i)
          {
            list.push_back(i);
          }
        },
        bad_alloc&);

#endif /* CVC4_MEMORY_LIMITING_DISABLED */
  }

  void testPopBelowLevelCreated()
  {
    d_context->push();
    CDList<int> list(d_context);
    d_context->popto(0);
    list.push_back(42);
  }
};
