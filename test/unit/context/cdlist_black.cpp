/*********************                                                        */
/*! \file cdlist_black.cpp
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

#include <limits.h>

#include <iostream>
#include <vector>

#include "base/exception.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "memory.h"
#include "test.h"

using namespace CVC4::context;
using namespace CVC4;

struct DtorSensitiveObject
{
  bool& d_dtorCalled;
  DtorSensitiveObject(bool& dtorCalled) : d_dtorCalled(dtorCalled) {}
  ~DtorSensitiveObject() { d_dtorCalled = true; }
};

class TestCDListBlack : public TestInternal
{
 protected:
  void SetUp() override { d_context = new Context(); }
  void TearDown() override { delete d_context; }

  void list_test(int n)
  {
    list_test(n, true);
    list_test(n, false);
  }

  void list_test(int32_t n, bool callDestructor)
  {
    CDList<int32_t> list(d_context, callDestructor);

    ASSERT_TRUE(list.empty());
    for (int32_t i = 0; i < n; ++i)
    {
      EXPECT_EQ(list.size(), (uint32_t)i);
      list.push_back(i);
      ASSERT_FALSE(list.empty());
      EXPECT_EQ(list.back(), i);
      int32_t i2 = 0;
      for (CDList<int32_t>::const_iterator j = list.begin(); j != list.end();
           ++j)
      {
        EXPECT_EQ(*j, i2++);
      }
    }
    EXPECT_EQ(list.size(), (uint32_t)n);

    for (int32_t i = 0; i < n; ++i)
    {
      EXPECT_EQ(list[i], i);
    }
  }

  Context* d_context;
};

TEST_F(TestCDListBlack, CDList10) { list_test(10); }

TEST_F(TestCDListBlack, CDList15) { list_test(15); }

TEST_F(TestCDListBlack, CDList20) { list_test(20); }

TEST_F(TestCDListBlack, CDList35) { list_test(35); }

TEST_F(TestCDListBlack, CDList50) { list_test(50); }

TEST_F(TestCDListBlack, CDList99) { list_test(99); }

TEST_F(TestCDListBlack, destructor_called)
{
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

  EXPECT_EQ(shouldRemainFalse, false);
  EXPECT_EQ(shouldFlipToTrue, false);
  EXPECT_EQ(alsoFlipToTrue, false);
  EXPECT_EQ(shouldAlsoRemainFalse, false);
  EXPECT_EQ(aThirdFalse, false);

  d_context->pop();

  EXPECT_EQ(shouldRemainFalse, false);
  EXPECT_EQ(shouldFlipToTrue, true);
  EXPECT_EQ(alsoFlipToTrue, true);
  EXPECT_EQ(shouldAlsoRemainFalse, false);
  EXPECT_EQ(aThirdFalse, false);
}

TEST_F(TestCDListBlack, empty_iterator)
{
  CDList<int>* list = new (true) CDList<int>(d_context);
  EXPECT_EQ(list->begin(), list->end());
  list->deleteSelf();
}

TEST_F(TestCDListBlack, out_of_memory)
{
#ifndef CVC4_MEMORY_LIMITING_DISABLED
  CDList<uint32_t> list(d_context);
  test::WithLimitedMemory wlm(1);

  ASSERT_THROW(
      {
        // We cap it at UINT32_MAX, preferring to terminate with a
        // failure than run indefinitely.
        for (uint32_t i = 0; i < UINT32_MAX; ++i)
        {
          list.push_back(i);
        }
      },
      std::bad_alloc);
#endif
}

TEST_F(TestCDListBlack, pop_below_level_created)
{
  d_context->push();
  CDList<int32_t> list(d_context);
  d_context->popto(0);
  list.push_back(42);
}
