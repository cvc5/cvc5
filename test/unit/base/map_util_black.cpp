/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of map utility functions.
 */

#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "base/map_util.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/context.h"
#include "test.h"

namespace cvc5::internal {

using cvc5::context::CDHashMap;
using cvc5::context::CDInsertHashMap;
using cvc5::context::Context;

namespace test {

class TestBaseBlackMap : public TestInternal
{
 protected:
  /** Returns a map containing {"key"->"value", "other"->"entry"}. */
  static const std::map<std::string, std::string>& default_map()
  {
    static const std::map<std::string, std::string> static_stored_map{
        {"key", "value"}, {"other", "entry"}};
    return static_stored_map;
  }

  /**
   * For each <key, value> pair in source, inserts mapping from key to value
   * using insert into dest.
   */
  template <class M>
  void insert_all(const std::map<std::string, std::string>& source, M* dest)
  {
    for (const auto& key_value : source)
    {
      dest->insert(key_value.first, key_value.second);
    }
  }
};

TEST_F(TestBaseBlackMap, map)
{
  std::map<std::string, std::string> map = default_map();
  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));

  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  if (std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
    *found_value = "new value";
  }
  ASSERT_EQ(FindOrDie(map, "other"), "new value");
}

TEST_F(TestBaseBlackMap, constant_map)
{
  const std::map<std::string, std::string> map = default_map();
  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
  }
  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  ASSERT_EQ(FindOrDie(map, "other"), "entry");
  ASSERT_DEATH(FindOrDie(map, "asdf"), "The map does not contain the key.");
}

TEST_F(TestBaseBlackMap, unordered_map)
{
  std::unordered_map<std::string, std::string> map(default_map().begin(),
                                                   default_map().end());
  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));

  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  if (std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
    *found_value = "new value";
  }
  ASSERT_EQ(FindOrDie(map, "other"), "new value");
}

TEST_F(TestBaseBlackMap, const_unordered_map)
{
  const std::unordered_map<std::string, std::string> map(default_map().begin(),
                                                         default_map().end());
  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
  }
  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  ASSERT_EQ(FindOrDie(map, "other"), "entry");
  ASSERT_DEATH(FindOrDie(map, "asdf"), "The map does not contain the key.");
}

TEST_F(TestBaseBlackMap, set)
{
  std::set<std::string> set{"entry", "other"};
  ASSERT_TRUE(ContainsKey(set, "entry"));
  ASSERT_FALSE(ContainsKey(set, "non member"));

  const std::set<std::string> const_set{"entry", "other"};
  ASSERT_TRUE(ContainsKey(const_set, "entry"));
  ASSERT_FALSE(ContainsKey(const_set, "non member"));
}

TEST_F(TestBaseBlackMap, unordered_set)
{
  std::unordered_set<std::string> set{"entry", "other"};
  ASSERT_TRUE(ContainsKey(set, "entry"));
  ASSERT_FALSE(ContainsKey(set, "non member"));

  const std::unordered_set<std::string> const_set{"entry", "other"};
  ASSERT_TRUE(ContainsKey(const_set, "entry"));
  ASSERT_FALSE(ContainsKey(const_set, "non member"));
}

TEST_F(TestBaseBlackMap, CDHashMap)
{
  Context context;
  CDHashMap<std::string, std::string> map(&context);
  insert_all(default_map(), &map);

  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
  }
  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  ASSERT_EQ(FindOrDie(map, "other"), "entry");
}

TEST_F(TestBaseBlackMap, const_CDHashMap)
{
  Context context;
  CDHashMap<std::string, std::string> store(&context);
  insert_all(default_map(), &store);
  const auto& map = store;

  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
  }
  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  ASSERT_EQ(FindOrDie(map, "other"), "entry");
}

TEST_F(TestBaseBlackMap, CDInsertHashMap)
{
  Context context;
  CDInsertHashMap<std::string, std::string> map(&context);
  insert_all(default_map(), &map);

  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
  }
  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  ASSERT_EQ(FindOrDie(map, "other"), "entry");
}

TEST_F(TestBaseBlackMap, const_CDInsertHashMap)
{
  Context context;
  CDInsertHashMap<std::string, std::string> store(&context);
  insert_all(default_map(), &store);
  const auto& map = store;

  ASSERT_TRUE(ContainsKey(map, "key"));
  ASSERT_FALSE(ContainsKey(map, "non key"));
  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    ASSERT_EQ(*found_value, "entry");
  }
  ASSERT_EQ(FindOrNull(map, "non key"), nullptr);
  ASSERT_EQ(FindOrDie(map, "other"), "entry");
}
}  // namespace test
}  // namespace cvc5::internal
