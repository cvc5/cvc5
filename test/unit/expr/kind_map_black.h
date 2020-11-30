/*********************                                                        */
/*! \file kind_map_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::KindMap
 **
 ** Black box testing of CVC4::KindMap.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <string>
#include <sstream>

#include "expr/kind_map.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class KindMapBlack : public CxxTest::TestSuite {

public:

  void testSimple() {
    KindMap map;
    TS_ASSERT(map.isEmpty());
    map.set(AND);
    TS_ASSERT(!map.isEmpty());
    KindMap map2 = map;
    TS_ASSERT(!map2.isEmpty());
    TS_ASSERT_EQUALS(map, map2);
    TS_ASSERT(map.tst(AND));
    TS_ASSERT(map2.tst(AND));
    TS_ASSERT(!map.tst(OR));
    TS_ASSERT(!map2.tst(OR));
    map2 = ~map2;
    TS_ASSERT(map2.tst(OR));
    TS_ASSERT(!map2.tst(AND));
    TS_ASSERT(map != map2);
    TS_ASSERT(map.begin() != map.end());
    TS_ASSERT(map2.begin() != map2.end());
    map &= ~AND;
    TS_ASSERT(map.isEmpty());
    map2.clear();
    TS_ASSERT(map2.isEmpty());
    TS_ASSERT_EQUALS(map2, map);
    TS_ASSERT_EQUALS(map.begin(), map.end());
    TS_ASSERT_EQUALS(map2.begin(), map2.end());
  }

  void testIteration() {
    KindMap m = AND & OR;
    TS_ASSERT(m.isEmpty());
    for(KindMap::iterator i = m.begin(); i != m.end(); ++i) {
      TS_FAIL("expected empty iterator range");
    }
    m = AND | OR;
    KindMap::iterator i = m.begin();
    TS_ASSERT(i != m.end());
    TS_ASSERT_EQUALS(*i, AND);
    ++i;
    TS_ASSERT(i != m.end());
    TS_ASSERT_EQUALS(*i, OR);
    ++i;
    TS_ASSERT(i == m.end());

    m = ~m;
    unsigned k = 0;
    for(i = m.begin(); i != m.end(); ++i, ++k) {
      while(k == AND || k == OR) {
        ++k;
      }
      TS_ASSERT_DIFFERS(Kind(k), UNDEFINED_KIND);
      TS_ASSERT_DIFFERS(Kind(k), LAST_KIND);
      TS_ASSERT_EQUALS(*i, Kind(k));
    }
  }

  void testConstruction() {
    TS_ASSERT(!(AND & AND).isEmpty());
    TS_ASSERT((AND & ~AND).isEmpty());
    TS_ASSERT(!(AND & AND & AND).isEmpty());

    TS_ASSERT(!(AND | AND).isEmpty());
    TS_ASSERT(!(AND | ~AND).isEmpty());
    TS_ASSERT(((AND | AND) & ~AND).isEmpty());
    TS_ASSERT(!((AND | OR) & ~AND).isEmpty());

    TS_ASSERT((AND ^ AND).isEmpty());
    TS_ASSERT(!(AND ^ OR).isEmpty());
    TS_ASSERT(!(AND ^ AND ^ AND).isEmpty());

#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS(~LAST_KIND, AssertArgumentException&);
#endif /* CVC4_ASSERTIONS */
  }

};/* class KindMapBlack */
