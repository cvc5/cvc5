/*********************                                                        */
/*! \file map_util_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

using CVC4::ContainsKey;
using CVC4::FindOrDie;
using CVC4::FindOrNull;
using CVC4::context::CDHashMap;
using CVC4::context::CDInsertHashMap;
using CVC4::context::Context;

class MapUtilBlack : public CxxTest::TestSuite
{
 public:
  void setUp() {}
  void tearDown() {}

  void testMap()
  {
    std::map<std::string, std::string> map{{"key", "value"},
                                           {"other", "entry"}};
    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    if (std::string* value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*value, "entry");
      *value = "new value";
    }
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "new value");
  }

  void testConstantMap()
  {
    const std::map<std::string, std::string> map{{"key", "value"},
                                                 {"other", "entry"}};
    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const std::string* value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*value, "entry");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "entry");
    // Cannot do death tests for FindOrDie.
  }

  void testUnorderedMap()
  {
    std::unordered_map<std::string, std::string> map{{"key", "value"},
                                                     {"other", "entry"}};
    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    if (std::string* value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*value, "entry");
      *value = "new value";
    }
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "new value");
  }

  void testSet()
  {
    const std::set<std::string> set{"entry", "other"};
    TS_ASSERT(ContainsKey(set, "entry"));
    TS_ASSERT(!ContainsKey(set, "non member"));
  }

  void testCDHashMap()
  {
    Context context;
    CDHashMap<std::string, std::string> map(&context);
    map["key"] = "value";
    map["other"] = "other value";

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const std::string* value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*value, "other value");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "other value");
  }

  void testConstCDHashMap()
  {
    Context context;
    CDHashMap<std::string, std::string> store(&context);
    store["key"] = "value";
    store["other"] = "other value";

    const auto& map = store;

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const std::string* value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*value, "other value");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "other value");
  }

  void testCDInsertHashMap()
  {
    Context context;
    CDInsertHashMap<std::string, std::string> map(&context);
    map.insert("key", "entry");
    map.insert("other", "other value");

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));

    if (const std::string* value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*value, "other value");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "other value");
  }

  void testConstCDInsertHashMap()
  {
    Context context;
    CDInsertHashMap<std::string, std::string> store(&context);
    store.insert("key", "value");
    store.insert("other", "other value");

    const auto& map = store;

    TS_ASSERT(ContainsKey(map, "key"));
    TS_ASSERT(!ContainsKey(map, "non key"));
    if (const std::string* value = FindOrNull(map, "other"))
    {
      TS_ASSERT_EQUALS(*value, "other value");
    }
    TS_ASSERT(FindOrNull(map, "non key") == nullptr);
    TS_ASSERT_EQUALS(FindOrDie(map, "other"), "other value");
  }

}; /* class DatatypeBlack */
