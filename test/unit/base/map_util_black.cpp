/*********************                                                        */
/*! \file map_util_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of map utility functions.
 **
 ** Black box testing of map utility functions.
 **/

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

namespace CVC4 {

using context::CDHashMap;
using context::CDInsertHashMap;
using context::Context;

namespace test {

class TestMapBlack : public TestInternal
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

TEST_F(TestMapBlack, map)
{
  std::map<std::string, std::string> map = default_map();
  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));

  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  if (std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
    *found_value = "new value";
  }
  EXPECT_EQ(FindOrDie(map, "other"), "new value");
}

TEST_F(TestMapBlack, constant_map)
{
  const std::map<std::string, std::string> map = default_map();
  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
  }
  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  EXPECT_EQ(FindOrDie(map, "other"), "entry");
  ASSERT_DEATH(FindOrDie(map, "asdf"), "The map does not contain the key.");
}

TEST_F(TestMapBlack, unordered_map)
{
  std::unordered_map<std::string, std::string> map(default_map().begin(),
                                                   default_map().end());
  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));

  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  if (std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
    *found_value = "new value";
  }
  EXPECT_EQ(FindOrDie(map, "other"), "new value");
}

TEST_F(TestMapBlack, const_unordered_map)
{
  const std::unordered_map<std::string, std::string> map(default_map().begin(),
                                                         default_map().end());
  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
  }
  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  EXPECT_EQ(FindOrDie(map, "other"), "entry");
  ASSERT_DEATH(FindOrDie(map, "asdf"), "The map does not contain the key.");
}

TEST_F(TestMapBlack, set)
{
  std::set<std::string> set{"entry", "other"};
  ASSERT_TRUE(CVC4::ContainsKey(set, "entry"));
  ASSERT_FALSE(CVC4::ContainsKey(set, "non member"));

  const std::set<std::string> const_set{"entry", "other"};
  ASSERT_TRUE(CVC4::ContainsKey(const_set, "entry"));
  ASSERT_FALSE(CVC4::ContainsKey(const_set, "non member"));
}

TEST_F(TestMapBlack, unordered_set)
{
  std::unordered_set<std::string> set{"entry", "other"};
  ASSERT_TRUE(CVC4::ContainsKey(set, "entry"));
  ASSERT_FALSE(CVC4::ContainsKey(set, "non member"));

  const std::unordered_set<std::string> const_set{"entry", "other"};
  ASSERT_TRUE(CVC4::ContainsKey(const_set, "entry"));
  ASSERT_FALSE(CVC4::ContainsKey(const_set, "non member"));
}

TEST_F(TestMapBlack, CDHashMap)
{
  Context context;
  CDHashMap<std::string, std::string> map(&context);
  insert_all(default_map(), &map);

  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
  }
  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  EXPECT_EQ(FindOrDie(map, "other"), "entry");
}

TEST_F(TestMapBlack, const_CDHashMap)
{
  Context context;
  CDHashMap<std::string, std::string> store(&context);
  insert_all(default_map(), &store);
  const auto& map = store;

  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
  }
  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  EXPECT_EQ(FindOrDie(map, "other"), "entry");
}

TEST_F(TestMapBlack, CDInsertHashMap)
{
  Context context;
  CDInsertHashMap<std::string, std::string> map(&context);
  insert_all(default_map(), &map);

  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));

  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
  }
  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  EXPECT_EQ(FindOrDie(map, "other"), "entry");
}

TEST_F(TestMapBlack, const_CDInsertHashMap)
{
  Context context;
  CDInsertHashMap<std::string, std::string> store(&context);
  insert_all(default_map(), &store);
  const auto& map = store;

  ASSERT_TRUE(CVC4::ContainsKey(map, "key"));
  ASSERT_FALSE(CVC4::ContainsKey(map, "non key"));
  if (const std::string* found_value = FindOrNull(map, "other"))
  {
    EXPECT_EQ(*found_value, "entry");
  }
  EXPECT_EQ(FindOrNull(map, "non key"), nullptr);
  EXPECT_EQ(FindOrDie(map, "other"), "entry");
}
}  // namespace test
}  // namespace CVC4
