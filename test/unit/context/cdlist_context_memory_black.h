/*********************                                                        */
/*! \file cdlist_context_memory_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::CDList<>.
 **
 ** Black box testing of CVC4::context::CDList<>.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <vector>

#include <limits.h>

#include "memory.h"

#include "context/cdchunk_list.h"
#include "context/context.h"

using namespace std;
using namespace CVC4::context;

struct DtorSensitiveObject {
  bool& d_dtorCalled;
  DtorSensitiveObject(bool& dtorCalled) : d_dtorCalled(dtorCalled) {}
  ~DtorSensitiveObject() { d_dtorCalled = true; }
};

class CDListContextMemoryBlack : public CxxTest::TestSuite {
 private:
  Context* d_context;

 public:
  void setUp() { d_context = new Context(); }

  void tearDown() { delete d_context; }

  // test at different sizes.  this triggers grow() behavior differently.
  // grow() was completely broken in revision 256
  void testCDChunkList10() { listTest(10); }
  void testCDChunkList15() { listTest(15); }
  void testCDChunkList20() { listTest(20); }
  void testCDChunkList35() { listTest(35); }
  void testCDChunkList50() { listTest(50); }
  void testCDChunkList99() { listTest(99); }

  void listTest(int N) {
    listTest(N, true);
    listTest(N, false);
  }

  void listTest(int N, bool callDestructor) {
    CDChunkList<int> list(d_context, callDestructor,
                          ContextMemoryAllocator<int>(d_context->getCMM()));

    TS_ASSERT(list.empty());
    for (int i = 0; i < N; ++i) {
      TS_ASSERT_EQUALS(list.size(), unsigned(i));
      list.push_back(i);
      TS_ASSERT(!list.empty());
      TS_ASSERT_EQUALS(list.back(), i);
      int i2 = 0;
      for (CDChunkList<int>::const_iterator j = list.begin(); j != list.end();
           ++j) {
        TS_ASSERT_EQUALS(*j, i2++);
      }
    }
    TS_ASSERT_EQUALS(list.size(), unsigned(N));

    for (int i = 0; i < N; ++i) {
      TS_ASSERT_EQUALS(list[i], i);
    }
  }

  void testEmptyIterator() {
    CDChunkList<int>* list = new (d_context->getCMM())
        CDChunkList<int>(true, d_context, false,
                         ContextMemoryAllocator<int>(d_context->getCMM()));
    TS_ASSERT_EQUALS(list->begin(), list->end());
  }

  void testDtorCalled() {
    bool shouldRemainFalse = false;
    bool shouldFlipToTrue = false;
    bool alsoFlipToTrue = false;
    bool shouldAlsoRemainFalse = false;
    bool aThirdFalse = false;

    CDChunkList<DtorSensitiveObject> listT(
        d_context, true,
        ContextMemoryAllocator<DtorSensitiveObject>(d_context->getCMM()));
    CDChunkList<DtorSensitiveObject> listF(
        d_context, false,
        ContextMemoryAllocator<DtorSensitiveObject>(d_context->getCMM()));

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

  void testOutOfMemory() {
#ifdef CVC4_MEMORY_LIMITING_DISABLED

    CVC4::test::WarnWithLimitedMemoryDisabledReason();

#else /* CVC4_MEMORY_LIMITING_DISABLED */

    CDChunkList<unsigned> list(d_context);
    CVC4::test::WithLimitedMemory wlm(1);

    TS_ASSERT_THROWS(
        {
          // We cap it at UINT_MAX, preferring to terminate with a
          // failure than run indefinitely.
          for (unsigned i = 0; i < UINT_MAX; ++i) {
            list.push_back(i);
          }
        },
        bad_alloc);

#endif /* CVC4_MEMORY_LIMITING_DISABLED */
  }
};
