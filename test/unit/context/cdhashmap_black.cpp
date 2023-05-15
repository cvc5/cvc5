/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::context::CDMap<>.
 */

#include <map>

#include "base/check.h"
#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "test_context.h"

namespace cvc5::internal {
namespace test {

using cvc5::context::CDHashMap;
using cvc5::context::Context;

class TestContextBlackCDHashMap : public TestContext
{
 protected:
  /** Returns the elements in a CDHashMap. */
  static std::map<int32_t, int32_t> get_elements(
      const CDHashMap<int32_t, int32_t>& map)
  {
    return std::map<int32_t, int32_t>{map.begin(), map.end()};
  }

  /**
   * Returns true if the elements in map are the same as expected.
   * NOTE: This is mostly to help the type checker for matching expected within
   *       a ASSERT_*.
   */
  static bool elements_are(const CDHashMap<int32_t, int32_t>& map,
                           const std::map<int32_t, int32_t>& expected)
  {
    return get_elements(map) == expected;
  }
};

TEST_F(TestContextBlackCDHashMap, simple_sequence)
{
  CDHashMap<int32_t, int32_t> map(d_context.get());
  ASSERT_TRUE(elements_are(map, {}));

  map.insert(3, 4);
  ASSERT_TRUE(elements_are(map, {{3, 4}}));

  {
    d_context->push();
    ASSERT_TRUE(elements_are(map, {{3, 4}}));

    map.insert(5, 6);
    map.insert(9, 8);
    ASSERT_TRUE(elements_are(map, {{3, 4}, {5, 6}, {9, 8}}));

    {
      d_context->push();
      ASSERT_TRUE(elements_are(map, {{3, 4}, {5, 6}, {9, 8}}));

      map.insert(1, 2);
      ASSERT_TRUE(elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));

      {
        d_context->push();
        ASSERT_TRUE(elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));

        map.insert(1, 45);

        ASSERT_TRUE(
            elements_are(map, {{1, 45}, {3, 4}, {5, 6}, {9, 8}}));
        map.insert(23, 324);

        ASSERT_TRUE(
            elements_are(map, {{1, 45}, {3, 4}, {5, 6}, {9, 8}, {23, 324}}));
        d_context->pop();
      }

      ASSERT_TRUE(
          elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));
      d_context->pop();
    }

    ASSERT_TRUE(elements_are(map, {{3, 4}, {5, 6}, {9, 8}}));
    d_context->pop();
  }

  ASSERT_TRUE(elements_are(map, {{3, 4}}));
}

TEST_F(TestContextBlackCDHashMap, simple_sequence_fewer_finds)
{
  // no intervening find() in this one (under the theory that this could trigger
  // a bug)
  CDHashMap<int, int> map(d_context.get());
  map.insert(3, 4);

  {
    d_context->push();

    map.insert(5, 6);
    map.insert(9, 8);

    {
      d_context->push();

      map.insert(1, 2);

      ASSERT_TRUE(elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));
      {
        d_context->push();
        d_context->pop();
      }

      d_context->pop();
    }

    d_context->pop();
  }
}

TEST_F(TestContextBlackCDHashMap, insert_at_context_level_zero)
{
  CDHashMap<int, int> map(d_context.get());

  map.insert(3, 4);

  ASSERT_TRUE(elements_are(map, {{3, 4}}));
  {
    d_context->push();
    ASSERT_TRUE(elements_are(map, {{3, 4}}));

    map.insert(5, 6);
    map.insert(9, 8);

    ASSERT_TRUE(elements_are(map, {{3, 4}, {5, 6}, {9, 8}}));

    {
      d_context->push();

      ASSERT_TRUE(elements_are(map, {{3, 4}, {5, 6}, {9, 8}}));

      map.insert(1, 2);

      ASSERT_TRUE(elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));

      ASSERT_TRUE(
          elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}}));

      map.insert(23, 472);

      ASSERT_TRUE(
          elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 472}}));
      {
        d_context->push();

        ASSERT_TRUE(
            elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 472}}));

        map.insert(23, 1024);

        ASSERT_TRUE(
            elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 1024}}));
        d_context->pop();
      }
      ASSERT_TRUE(
          elements_are(map, {{1, 2}, {3, 4}, {5, 6}, {9, 8}, {23, 472}}));
      d_context->pop();
    }

    ASSERT_TRUE(elements_are(map, {{3, 4}, {5, 6}, {9, 8}}));

    map.insert(23, 477);

    ASSERT_TRUE(elements_are(map, {{3, 4}, {5, 6}, {9, 8}, {23, 477}}));
    d_context->pop();
  }

  ASSERT_TRUE(elements_are(map, {{3, 4}}));
}
}  // namespace test
}  // namespace cvc5::internal
