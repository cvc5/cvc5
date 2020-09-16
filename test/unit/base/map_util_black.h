/*********************                                                        */
/*! \file map_util_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli
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

#include <cxxtest/TestSuite.h>
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

using CVC4::ContainsKey;
using CVC4::FindOrDie;
using CVC4::FindOrNull;
using CVC4::context::CDHashMap;
using CVC4::context::CDInsertHashMap;
using CVC4::context::Context;
using std::string;

class MapUtilBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  // Returns a map containing {"key"->"value", "other"->"entry"}.
  static const std::map<string, string>& DefaultMap()
  {
    static const std::map<string, string> static_stored_map{{"key", "value"},
                                                            {"other", "entry"}};
    return static_stored_map;
  }

  void testMap()
  {
    std::map<string, string> map = DefaultMap();
    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    if (string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
      *found_value = "new value";
    }
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "new value");
  }

  void testConstantMap()
  {
    const std::map<string, string> map = DefaultMap();
    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "entry");
    // Cannot do death tests for FindOrDie.
  }

  void testUnorderedMap()
  {
    std::unordered_map<string, string> map(DefaultMap().begin(),
                                           DefaultMap().end());
    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    if (string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
      *found_value = "new value";
    }
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "new value");
  }

  void testConstUnorderedMap()
  {
    const std::unordered_map<string, string> map(DefaultMap().begin(),
                                                 DefaultMap().end());
    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "entry");
    // Cannot do death tests for FindOrDie.
  }

  void testSet()
  {
    std::set<string> set{"entry", "other"};
    TS_ASSERT(ContainsKey(set, "entry"));
    TS_ASSERT(!ContainsKey(set, "non member"));

    const std::set<string> const_set{"entry", "other"};
    TS_ASSERT(ContainsKey(const_set, "entry"));
    TS_ASSERT(!ContainsKey(const_set, "non member"));
  }

  void testUnorderedSet()
  {
    std::unordered_set<string> set{"entry", "other"};
    TS_ASSERT(ContainsKey(set, "entry"));
    TS_ASSERT(!ContainsKey(set, "non member"));

    const std::unordered_set<string> const_set{"entry", "other"};
    TS_ASSERT(ContainsKey(const_set, "entry"));
    TS_ASSERT(!ContainsKey(const_set, "non member"));
  }

  // For each <key, value> pair in source, inserts mapping from key to value
  // using insert into dest.
  template <class M>
  void InsertAll(const std::map<string, string>& source, M* dest)
  {
    for (const auto& key_value : source)
    {
      dest->insert(key_value.first, key_value.second);
    }
  }

  void testCDHashMap()
  {
    Context context;
    CDHashMap<string, string> map(&context);
    InsertAll(DefaultMap(), &map);

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "entry");
  }

  void testConstCDHashMap()
  {
    Context context;
    CDHashMap<string, string> store(&context);
    InsertAll(DefaultMap(), &store);
    const auto& map = store;

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "entry");
  }

  void testCDInsertHashMap()
  {
    Context context;
    CDInsertHashMap<string, string> map(&context);
    InsertAll(DefaultMap(), &map);

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "entry");
  }

  void testConstCDInsertHashMap()
  {
    Context context;
    CDInsertHashMap<string, string> store(&context);
    InsertAll(DefaultMap(), &store);
    const auto& map = store;

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));
    if (const string* found_value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*found_value, "entry");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "entry");
  }

}; /* class MapUtilBlack */
