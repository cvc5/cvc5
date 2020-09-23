/*********************                                                        */
/*! \file binary_heap_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::BinaryHeap
 **
 ** Black box testing of CVC4::BinaryHeap.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <sstream>

#include "test_utils.h"
#include "util/bin_heap.h"

using namespace CVC4;
using namespace std;

class BinaryHeapBlack : public CxxTest::TestSuite {
 public:
  void setUp() override {}

  void tearDown() override {}

  /**
   * Test a a series of simple heaps (push a few then pop all then do others).
   * Done as a series to test if the heap structure falls into a bad state
   * after prolonged use.
   */
  void testHeapSeries()
  {
    BinaryHeap<int> heap;

    // First test a heap of 1 element
    TS_ASSERT_EQUALS(heap.size(), 0u);
    TS_ASSERT(heap.empty());
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(heap.top());
    TS_UTILS_EXPECT_ABORT(heap.pop());
#endif /* CVC4_ASSERTIONS */
    TS_ASSERT_EQUALS(heap.begin(), heap.end());

    BinaryHeap<int>::handle h5 = heap.push(5);
    TS_ASSERT(h5 == h5);
    TS_ASSERT_EQUALS(heap.top(), 5);
    TS_ASSERT_EQUALS(heap.size(), 1u);
    TS_ASSERT(! heap.empty());
    TS_ASSERT_DIFFERS(heap.begin(), heap.end());
    TS_ASSERT_EQUALS(*h5, 5);
    TS_ASSERT_EQUALS(*heap.begin(), 5);
    TS_ASSERT_THROWS_NOTHING(heap.erase(h5));
    TS_ASSERT(heap.empty());
    TS_ASSERT_EQUALS(heap.size(), 0u);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(heap.top());
    TS_UTILS_EXPECT_ABORT(heap.pop());
#endif /* CVC4_ASSERTIONS */

    // Next test a heap of 4 elements
    h5 = heap.push(5);
    BinaryHeap<int>::handle h3 = heap.push(3);
    BinaryHeap<int>::handle h10 = heap.push(10);
    BinaryHeap<int>::handle h2 = heap.push(2);
    TS_ASSERT_DIFFERS(h5, h3);
    TS_ASSERT_DIFFERS(h5, h10);
    TS_ASSERT_DIFFERS(h5, h2);
    TS_ASSERT_DIFFERS(h3, h10);
    TS_ASSERT_DIFFERS(h3, h2);
    TS_ASSERT_DIFFERS(h10, h2);
    TS_ASSERT_DIFFERS(heap.begin(), heap.end());
    TS_ASSERT_EQUALS(*heap.begin(), 10);
    TS_ASSERT_EQUALS(*h2, 2);
    TS_ASSERT_EQUALS(*h3, 3);
    TS_ASSERT_EQUALS(*h5, 5);
    TS_ASSERT_EQUALS(*h10, 10);
    TS_ASSERT_EQUALS(heap.top(), 10);
    // test the iterator (note the order of elements isn't guaranteed!)
    BinaryHeap<int>::const_iterator i = heap.begin();
    TS_ASSERT_DIFFERS(i, heap.end());
    TS_ASSERT_THROWS_NOTHING(*i++);
    TS_ASSERT_DIFFERS(i, heap.end());
    TS_ASSERT_THROWS_NOTHING(*i++);
    TS_ASSERT_DIFFERS(i, heap.end());
    TS_ASSERT_THROWS_NOTHING(*i++);
    TS_ASSERT_DIFFERS(i, heap.end());
    TS_ASSERT_THROWS_NOTHING(*i++);
    TS_ASSERT_EQUALS(i, heap.end());
    TS_ASSERT(!heap.empty());
    TS_ASSERT_EQUALS(heap.size(), 4u);
    TS_ASSERT_THROWS_NOTHING(heap.pop());
    TS_ASSERT_DIFFERS(heap.begin(), heap.end());
    TS_ASSERT_EQUALS(*heap.begin(), 5);
    TS_ASSERT_EQUALS(heap.top(), 5);
    TS_ASSERT(!heap.empty());
    TS_ASSERT_EQUALS(heap.size(), 3u);
    TS_ASSERT_THROWS_NOTHING(heap.pop());
    TS_ASSERT_DIFFERS(heap.begin(), heap.end());
    TS_ASSERT_EQUALS(*heap.begin(), 3);
    TS_ASSERT_EQUALS(heap.top(), 3);
    TS_ASSERT(!heap.empty());
    TS_ASSERT_EQUALS(heap.size(), 2u);
    TS_ASSERT_THROWS_NOTHING(heap.pop());
    TS_ASSERT_DIFFERS(heap.begin(), heap.end());
    TS_ASSERT_EQUALS(*heap.begin(), 2);
    TS_ASSERT_EQUALS(heap.top(), 2);
    TS_ASSERT(!heap.empty());
    TS_ASSERT_EQUALS(heap.size(), 1u);
    TS_ASSERT_THROWS_NOTHING(heap.pop());
    TS_ASSERT_EQUALS(heap.begin(), heap.end());
    TS_ASSERT(heap.empty());
    TS_ASSERT_EQUALS(heap.size(), 0u);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(heap.top());
    TS_UTILS_EXPECT_ABORT(heap.pop());
#endif /* CVC4_ASSERTIONS */

    // Now with a few updates
    h5 = heap.push(5);
    h3 = heap.push(3);
    h10 = heap.push(10);
    h2 = heap.push(2);

    TS_ASSERT_EQUALS(*h5, 5);
    TS_ASSERT_EQUALS(*h3, 3);
    TS_ASSERT_EQUALS(*h10, 10);
    TS_ASSERT_EQUALS(*h2, 2);

    TS_ASSERT_EQUALS(heap.top(), 10);
    heap.update(h10, -10);
    TS_ASSERT_EQUALS(*h10, -10);
    TS_ASSERT_EQUALS(heap.top(), 5);
    heap.erase(h2);
    TS_ASSERT_EQUALS(heap.top(), 5);
    heap.update(h3, -20);
    TS_ASSERT_EQUALS(*h3, -20);
    TS_ASSERT_EQUALS(heap.top(), 5);
    heap.pop();
    TS_ASSERT_EQUALS(heap.top(), -10);
    heap.pop();
    TS_ASSERT_EQUALS(heap.top(), -20);
  }

  struct Elem {
    int x;
    Elem(int y) : x(y) {}
  };/* struct Elem */

  struct Cmp {
    bool valid;
    Cmp() : valid(false) {}
    Cmp(int x) : valid(true) {}
    bool operator()(Elem x, Elem y) const {
      // ensure BinaryHeap<> calls our Cmp instance and not some fresh one
      TS_ASSERT(valid);
      return x.x > y.x;
    }
  };/* struct Cmp */

  void testLargeHeap() {
    BinaryHeap<Elem, Cmp> heap(Cmp(0));
    vector<BinaryHeap<Elem, Cmp>::handle> handles;
    TS_ASSERT(heap.empty());
    for(int x = 0; x < 1000; ++x) {
      handles.push_back(heap.push(Elem(x)));
    }
    TS_ASSERT(!heap.empty());
    TS_ASSERT_EQUALS(heap.size(), 1000u);
    heap.update(handles[100], 50);
    heap.update(handles[100], -50);
    heap.update(handles[600], 2);
    heap.update(handles[184], -9);
    heap.update(handles[987], 9555);
    heap.update(handles[672], -1003);
    heap.update(handles[781], 481);
    heap.update(handles[9], 9619);
    heap.update(handles[919], 111);
    TS_ASSERT_EQUALS(heap.size(), 1000u);
    heap.erase(handles[10]);
    TS_ASSERT_EQUALS(heap.size(), 999u);
    TS_ASSERT(!heap.empty());
    handles.clear();
    Elem last = heap.top();
    for(int x = 0; x < 800; ++x) {
      TS_ASSERT_LESS_THAN_EQUALS(last.x, heap.top().x);
      last = heap.top();
      heap.pop();
      TS_ASSERT_EQUALS(heap.size(), 998u - x);
      TS_ASSERT(!heap.empty());
    }
    TS_ASSERT_EQUALS(heap.size(), 199u);
    for(int x = 0; x < 10000; ++x) {
      // two-thirds of the time insert large value, one-third insert small value
      handles.push_back(heap.push(Elem(4 * ((x % 3 == 0) ? -x : x))));
      if(x % 10 == 6) {
        // also every tenth insert somewhere in the middle
        handles.push_back(heap.push(Elem(x / 10)));
      }
      // change a few
      heap.update(handles[x / 10], 4 * (*handles[x / 10]).x);
      heap.update(handles[x / 105], (*handles[x / 4]).x - 294);
      heap.update(handles[x / 33], 6 * (*handles[x / 82]).x / 5 - 1);
      TS_ASSERT_EQUALS(heap.size(), size_t(x) + ((x + 4) / 10) + 200);
    }
    TS_ASSERT_EQUALS(heap.size(), 11199u);
    TS_ASSERT(!heap.empty());
    last = heap.top();
    while(!heap.empty()) {
      TS_ASSERT_LESS_THAN_EQUALS(last.x, heap.top().x);
      last = heap.top();
      heap.pop();
    }
    TS_ASSERT(heap.empty());
    heap.clear();
    TS_ASSERT(heap.empty());
  }

};/* class BinaryHeapBlack */
