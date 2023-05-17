/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::context::CDList<>.
 */

#include <limits.h>

#include <iostream>
#include <vector>

#include "base/exception.h"
#include "context/cdlist.h"
#include "test_context.h"

namespace cvc5::internal {

using namespace context;

namespace test {

class TestObject
{
 public:
  // Test support for elements without default constructor
  TestObject() = delete;

  TestObject(bool* cleanupCalled) : d_cleanupCalled(cleanupCalled) {}

  bool* d_cleanupCalled;
};

class TestCleanup
{
 public:
  TestCleanup() {}
  void operator()(TestObject& o) { (*o.d_cleanupCalled) = true; }
};

class TestContextBlackCDList : public TestContext
{
 protected:
  void list_test(int n)
  {
    list_test(n, true);
    list_test(n, false);
  }

  void list_test(int32_t n, bool callDestructor)
  {
    CDList<int32_t> list(d_context.get(), callDestructor);

    ASSERT_TRUE(list.empty());
    for (int32_t i = 0; i < n; ++i)
    {
      ASSERT_EQ(list.size(), (uint32_t)i);
      list.push_back(i);
      ASSERT_FALSE(list.empty());
      ASSERT_EQ(list.back(), i);
      int32_t i2 = 0;
      for (CDList<int32_t>::const_iterator j = list.begin(); j != list.end();
           ++j)
      {
        ASSERT_EQ(*j, i2++);
      }
    }
    ASSERT_EQ(list.size(), (uint32_t)n);

    for (int32_t i = 0; i < n; ++i)
    {
      ASSERT_EQ(list[i], i);
    }
  }
};

TEST_F(TestContextBlackCDList, CDList10) { list_test(10); }

TEST_F(TestContextBlackCDList, CDList15) { list_test(15); }

TEST_F(TestContextBlackCDList, CDList20) { list_test(20); }

TEST_F(TestContextBlackCDList, CDList35) { list_test(35); }

TEST_F(TestContextBlackCDList, CDList50) { list_test(50); }

TEST_F(TestContextBlackCDList, CDList99) { list_test(99); }

TEST_F(TestContextBlackCDList, destructor_called)
{
  bool shouldRemainFalse = false;
  bool shouldFlipToTrue = false;
  bool alsoFlipToTrue = false;
  bool shouldAlsoRemainFalse = false;
  bool aThirdFalse = false;

  CDList<TestObject, TestCleanup> listT(d_context.get(), true, TestCleanup());
  CDList<TestObject, TestCleanup> listF(d_context.get(), false, TestCleanup());

  TestObject shouldRemainFalseDSO(&shouldRemainFalse);
  TestObject shouldFlipToTrueDSO(&shouldFlipToTrue);
  TestObject alsoFlipToTrueDSO(&alsoFlipToTrue);
  TestObject shouldAlsoRemainFalseDSO(&shouldAlsoRemainFalse);
  TestObject aThirdFalseDSO(&aThirdFalse);

  listT.push_back(shouldAlsoRemainFalseDSO);
  listF.push_back(shouldAlsoRemainFalseDSO);

  d_context->push();

  listT.push_back(shouldFlipToTrueDSO);
  listT.push_back(alsoFlipToTrueDSO);

  listF.push_back(shouldRemainFalseDSO);
  listF.push_back(shouldAlsoRemainFalseDSO);
  listF.push_back(aThirdFalseDSO);

  ASSERT_EQ(shouldRemainFalse, false);
  ASSERT_EQ(shouldFlipToTrue, false);
  ASSERT_EQ(alsoFlipToTrue, false);
  ASSERT_EQ(shouldAlsoRemainFalse, false);
  ASSERT_EQ(aThirdFalse, false);

  d_context->pop();

  ASSERT_EQ(shouldRemainFalse, false);
  ASSERT_EQ(shouldFlipToTrue, true);
  ASSERT_EQ(alsoFlipToTrue, true);
  ASSERT_EQ(shouldAlsoRemainFalse, false);
  ASSERT_EQ(aThirdFalse, false);
}

TEST_F(TestContextBlackCDList, empty_iterator)
{
  CDList<int>* list = new (true) CDList<int>(d_context.get());
  ASSERT_EQ(list->begin(), list->end());
  list->deleteSelf();
}

TEST_F(TestContextBlackCDList, pop_below_level_created)
{
  d_context->push();
  CDList<int32_t> list(d_context.get());
  d_context->popto(0);
  list.push_back(42);
}

TEST_F(TestContextBlackCDList, emplace_back)
{
  int32_t n = 10;
  int32_t start = 42;
  CDList<std::unique_ptr<int32_t>> list(d_context.get());

  for (int32_t i = 0; i < n; i++)
  {
    list.emplace_back(new int32_t(start + i));
  }
  for (int32_t i = 0; i < n; i++)
  {
    ASSERT_EQ(*list[i], start + i);
  }
  ASSERT_EQ(list.size(), n);

  d_context->push();
  for (int32_t i = 0; i < n; i++)
  {
    list.emplace_back(new int32_t(start + n + i));
  }
  for (int32_t i = 0; i < n * 2; i++)
  {
    ASSERT_EQ(*list[i], start + i);
  }
  ASSERT_EQ(list.size(), n * 2);
  d_context->pop();

  for (int32_t i = 0; i < n; i++)
  {
    ASSERT_EQ(*list[i], start + i);
  }
  ASSERT_EQ(list.size(), n);
}

}  // namespace test
}  // namespace cvc5::internal
