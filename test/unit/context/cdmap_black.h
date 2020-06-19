/*********************                                                        */
/*! \file cdmap_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::CDMap<>.
 **
 ** Black box testing of CVC4::context::CDMap<>.
 **/

#include <cxxtest/TestSuite.h>

#include <map>

#include "base/check.h"
#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "test_utils.h"

using CVC4::context::Context;
using CVC4::context::CDHashMap;

class CDMapBlack : public CxxTest::TestSuite {
  Context* d_context;

 public:
  void setUp() override
  {
    d_context = new Context;
    // Debug.on("context");
    // Debug.on("gc");
    // Debug.on("pushpop");
  }

  void tearDown() override { delete d_context; }

  // Returns the elements in a CDHashMap.
  static std::map<int, int> GetElements(const CDHashMap<int, int>& map) {
    return std::map<int, int>{map.begin(), map.end()};
  }

  // Returns true if the elements in map are the same as expected.
  // NOTE: This is mostly to help the type checker for matching expected within
  // a TS_ASSERT.
  static bool ElementsAre(const CDHashMap<int, int>& map,
                          const std::map<int, int>& expected) {
    return GetElements(map) == expected;
  }

  void testSimpleSequence() {
    CDHashMap<int, int> map(d_context);
    TS_ASSERT(ElementsAre(map, {}));

    map.insert(3, 4);
    TS_ASSERT(ElementsAre(map, {{3, 4}}));

    {
      d_context->push();
      TS_ASSERT(ElementsAre(map, {{3, 4}}));

      map.insert(5, 6);
      map.insert(9, 8);
      TS_ASSERT(ElementsAre(map, {{3, 4}, {5, 6}, {9, 8}}));

      {
        d_context->push();
        TS_ASSERT(ElementsAre(map, {{3, 4}, {5, 6}, {9, 8}}));

        map.insert(1, 2);
        TS_ASSERT(ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));

        {
          d_context->push();
          TS_ASSERT(ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));

          map.insertAtContextLevelZero(23, 317);
          map.insert(1, 45);

          TS_ASSERT(
              ElementsAre(map, {{1, 45}, {3, 4}, {5, 6}, {9, 8}, {23, 317}}));
          map.insert(23, 324);

          TS_ASSERT(
              ElementsAre(map, {{1, 45}, {3, 4}, {5, 6}, {9, 8}, {23, 324}}));
          d_context->pop();
        }

        TS_ASSERT(
            ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 317}}));
        d_context->pop();
      }

      TS_ASSERT(ElementsAre(map, {{3, 4}, {5, 6}, {9, 8}, {23, 317}}));
      d_context->pop();
    }

    TS_ASSERT(ElementsAre(map, {{3, 4}, {23, 317}}));
  }

  // no intervening find() in this one
  // (under the theory that this could trigger a bug)
  void testSimpleSequenceFewerFinds() {
    CDHashMap<int, int> map(d_context);
    map.insert(3, 4);

    {
      d_context->push();

      map.insert(5, 6);
      map.insert(9, 8);

      {
        d_context->push();

        map.insert(1, 2);

        TS_ASSERT(ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));
        {
          d_context->push();
          d_context->pop();
        }

        d_context->pop();
      }

      d_context->pop();
    }
  }

  void testInsertAtContextLevelZero() {
    CDHashMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(ElementsAre(map, {{3, 4}}));
    {
      d_context->push();
      TS_ASSERT(ElementsAre(map, {{3, 4}}));

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(ElementsAre(map, {{3, 4}, {5, 6}, {9, 8}}));

      {
        d_context->push();

        TS_ASSERT(ElementsAre(map, {{3, 4}, {5, 6}, {9, 8}}));

        map.insert(1, 2);

        TS_ASSERT(ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));

        map.insertAtContextLevelZero(23, 317);

        TS_ASSERT(
            ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 317}}));

        TS_UTILS_EXPECT_ABORT(map.insertAtContextLevelZero(23, 317));
        TS_UTILS_EXPECT_ABORT(map.insertAtContextLevelZero(23, 472));
        map.insert(23, 472);

        TS_ASSERT(
            ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 472}}));
        {
          d_context->push();

          TS_ASSERT(
            ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 472}}));

          TS_UTILS_EXPECT_ABORT(map.insertAtContextLevelZero(23, 0));
          map.insert(23, 1024);

          TS_ASSERT(
            ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 1024}}));
          d_context->pop();
        }
        TS_ASSERT(
            ElementsAre(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 472}}));
        d_context->pop();
      }


      TS_ASSERT(
          ElementsAre(map, {{3, 4}, {5, 6}, {9, 8}, {23, 317}}));

      TS_UTILS_EXPECT_ABORT(map.insertAtContextLevelZero(23, 0));
      map.insert(23, 477);

      TS_ASSERT(
          ElementsAre(map, {{3, 4}, {5, 6}, {9, 8}, {23, 477}}));
      d_context->pop();
    }

    TS_UTILS_EXPECT_ABORT(map.insertAtContextLevelZero(23, 0));

    TS_ASSERT(
        ElementsAre(map, {{3, 4}, {23, 317}}));
  }
};
