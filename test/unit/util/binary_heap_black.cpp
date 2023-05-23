/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::BinaryHeap.
 */

#include <iostream>
#include <sstream>

#include "test.h"
#include "util/bin_heap.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackBinaryHeap : public TestInternal
{
 protected:
  struct Elem
  {
    Elem(int32_t y) : d_x(y) {}
    int32_t d_x;
  };

  struct Cmp
  {
    Cmp() : d_valid(false) {}
    Cmp(int32_t x) : d_valid(true) {}

    bool operator()(Elem x, Elem y) const
    {
      // ensure BinaryHeap<> calls our Cmp instance and not some fresh one
      Assert(d_valid);
      return x.d_x > y.d_x;
    }

    bool d_valid;
  };
};

/**
 * Test a a series of simple heaps (push a few then pop all then do others).
 * Done as a series to test if the heap structure falls into a bad state
 * after prolonged use.
 */
TEST_F(TestUtilBlackBinaryHeap, heap_series)
{
  BinaryHeap<int32_t> heap;

  // First test a heap of 1 element
  ASSERT_EQ(heap.size(), 0u);
  ASSERT_TRUE(heap.empty());
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(heap.top(), "!empty\\(\\)");
  ASSERT_DEATH(heap.pop(), "!empty\\(\\)");
#endif
  ASSERT_TRUE(heap.begin() == heap.end());

  BinaryHeap<int32_t>::handle h5 = heap.push(5);
  ASSERT_TRUE(h5 == h5);
  ASSERT_EQ(heap.top(), 5);
  ASSERT_EQ(heap.size(), 1u);
  ASSERT_FALSE(heap.empty());
  ASSERT_TRUE(heap.begin() != heap.end());
  ASSERT_EQ(*h5, 5);
  ASSERT_EQ(*heap.begin(), 5);
  ASSERT_NO_THROW(heap.erase(h5));
  ASSERT_TRUE(heap.empty());
  ASSERT_EQ(heap.size(), 0u);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(heap.top(), "!empty\\(\\)");
  ASSERT_DEATH(heap.pop(), "!empty\\(\\)");
#endif

  // Next test a heap of 4 elements
  h5 = heap.push(5);
  BinaryHeap<int32_t>::handle h3 = heap.push(3);
  BinaryHeap<int32_t>::handle h10 = heap.push(10);
  BinaryHeap<int32_t>::handle h2 = heap.push(2);
  ASSERT_NE(h5, h3);
  ASSERT_NE(h5, h10);
  ASSERT_NE(h5, h2);
  ASSERT_NE(h3, h10);
  ASSERT_NE(h3, h2);
  ASSERT_NE(h10, h2);
  ASSERT_TRUE(heap.begin() != heap.end());
  ASSERT_EQ(*heap.begin(), 10);
  ASSERT_EQ(*h2, 2);
  ASSERT_EQ(*h3, 3);
  ASSERT_EQ(*h5, 5);
  ASSERT_EQ(*h10, 10);
  ASSERT_EQ(heap.top(), 10);
  // test the iterator (note the order of elements isn't guaranteed!)
  BinaryHeap<int32_t>::const_iterator i = heap.begin();
  ASSERT_TRUE(i != heap.end());
  ASSERT_NO_THROW(*i++);
  ASSERT_TRUE(i != heap.end());
  ASSERT_NO_THROW(*i++);
  ASSERT_TRUE(i != heap.end());
  ASSERT_NO_THROW(*i++);
  ASSERT_TRUE(i != heap.end());
  ASSERT_NO_THROW(*i++);
  ASSERT_TRUE(i == heap.end());
  ASSERT_FALSE(heap.empty());
  ASSERT_EQ(heap.size(), 4u);
  ASSERT_NO_THROW(heap.pop());
  ASSERT_TRUE(i != heap.end());
  ASSERT_EQ(*heap.begin(), 5);
  ASSERT_EQ(heap.top(), 5);
  ASSERT_FALSE(heap.empty());
  ASSERT_EQ(heap.size(), 3u);
  ASSERT_NO_THROW(heap.pop());
  ASSERT_TRUE(heap.begin() != heap.end());
  ASSERT_EQ(*heap.begin(), 3);
  ASSERT_EQ(heap.top(), 3);
  ASSERT_FALSE(heap.empty());
  ASSERT_EQ(heap.size(), 2u);
  ASSERT_NO_THROW(heap.pop());
  ASSERT_TRUE(heap.begin() != heap.end());
  ASSERT_EQ(*heap.begin(), 2);
  ASSERT_EQ(heap.top(), 2);
  ASSERT_FALSE(heap.empty());
  ASSERT_EQ(heap.size(), 1u);
  ASSERT_NO_THROW(heap.pop());
  ASSERT_TRUE(heap.begin() == heap.end());
  ASSERT_TRUE(heap.empty());
  ASSERT_EQ(heap.size(), 0u);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(heap.top(), "!empty\\(\\)");
  ASSERT_DEATH(heap.pop(), "!empty\\(\\)");
#endif

  // Now with a few updates
  h5 = heap.push(5);
  h3 = heap.push(3);
  h10 = heap.push(10);
  h2 = heap.push(2);

  ASSERT_EQ(*h5, 5);
  ASSERT_EQ(*h3, 3);
  ASSERT_EQ(*h10, 10);
  ASSERT_EQ(*h2, 2);

  ASSERT_EQ(heap.top(), 10);
  heap.update(h10, -10);
  ASSERT_EQ(*h10, -10);
  ASSERT_EQ(heap.top(), 5);
  heap.erase(h2);
  ASSERT_EQ(heap.top(), 5);
  heap.update(h3, -20);
  ASSERT_EQ(*h3, -20);
  ASSERT_EQ(heap.top(), 5);
  heap.pop();
  ASSERT_EQ(heap.top(), -10);
  heap.pop();
  ASSERT_EQ(heap.top(), -20);
}

TEST_F(TestUtilBlackBinaryHeap, large_heap)
{
  BinaryHeap<Elem, Cmp> heap(Cmp(0));
  std::vector<BinaryHeap<Elem, Cmp>::handle> handles;
  ASSERT_TRUE(heap.empty());
  for (int32_t x = 0; x < 1000; ++x)
  {
    handles.push_back(heap.push(Elem(x)));
  }
  ASSERT_FALSE(heap.empty());
  ASSERT_EQ(heap.size(), 1000u);
  heap.update(handles[100], 50);
  heap.update(handles[100], -50);
  heap.update(handles[600], 2);
  heap.update(handles[184], -9);
  heap.update(handles[987], 9555);
  heap.update(handles[672], -1003);
  heap.update(handles[781], 481);
  heap.update(handles[9], 9619);
  heap.update(handles[919], 111);
  ASSERT_EQ(heap.size(), 1000u);
  heap.erase(handles[10]);
  ASSERT_EQ(heap.size(), 999u);
  ASSERT_FALSE(heap.empty());
  handles.clear();
  Elem last = heap.top();
  for (int32_t x = 0; x < 800; ++x)
  {
    ASSERT_LE(last.d_x, heap.top().d_x);
    last = heap.top();
    heap.pop();
    ASSERT_EQ(heap.size(), 998u - x);
    ASSERT_FALSE(heap.empty());
  }
  ASSERT_EQ(heap.size(), 199u);
  for (int32_t x = 0; x < 10000; ++x)
  {
    // two-thirds of the time insert large value, one-third insert small value
    handles.push_back(heap.push(Elem(4 * ((x % 3 == 0) ? -x : x))));
    if (x % 10 == 6)
    {
      // also every tenth insert somewhere in the middle
      handles.push_back(heap.push(Elem(x / 10)));
    }
    // change a few
    heap.update(handles[x / 10], 4 * (*handles[x / 10]).d_x);
    heap.update(handles[x / 105], (*handles[x / 4]).d_x - 294);
    heap.update(handles[x / 33], 6 * (*handles[x / 82]).d_x / 5 - 1);
    ASSERT_EQ(heap.size(), size_t(x) + ((x + 4) / 10) + 200);
  }
  ASSERT_EQ(heap.size(), 11199u);
  ASSERT_FALSE(heap.empty());
  last = heap.top();
  while (!heap.empty())
  {
    ASSERT_LE(last.d_x, heap.top().d_x);
    last = heap.top();
    heap.pop();
  }
  ASSERT_TRUE(heap.empty());
  heap.clear();
  ASSERT_TRUE(heap.empty());
}
}  // namespace test
}  // namespace cvc5::internal
