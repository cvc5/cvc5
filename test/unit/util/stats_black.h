/*********************                                                        */
/*! \file stats_black.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Stat and associated classes
 **
 ** Black box testing of CVC4::Stat and associated classes.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>
#include <string>
#include <ctime>

#include "util/statistics_registry.h"

using namespace CVC4;
using namespace std;

class StatsBlack : public CxxTest::TestSuite {
public:

  void testStats() {
#ifdef CVC4_STATISTICS_ON
    // StatisticsRegistry
    //static void flushStatistics(std::ostream& out);

    //static inline void registerStat(Stat* s) throw (AssertionException);
    //static inline void unregisterStat(Stat* s) throw (AssertionException);

    string empty, bar = "bar", baz = "baz";
    ReferenceStat<string> refStr("stat #1", empty);
    ReferenceStat<string> refStr2("refStr2", bar);
    // setData
    // getData

    // flushInformation
    // flushStat

    BackedStat<string> backedStr("backed", baz);
    // setData
    // getData
    // operator=

    IntStat sInt("my int", 10);
    TimerStat sTimer("a timer ! for measuring time");

    TS_ASSERT_EQUALS(refStr.getName(), "stat #1");
    TS_ASSERT_EQUALS(refStr2.getName(), "refStr2");
    TS_ASSERT_EQUALS(backedStr.getName(), "backed");
    TS_ASSERT_EQUALS(sInt.getName(), "my int");
    TS_ASSERT_EQUALS(sTimer.getName(), "a timer ! for measuring time");

    TS_ASSERT_EQUALS(refStr.getData(), empty);
    TS_ASSERT_EQUALS(refStr2.getData(), bar);
    empty = "a different string";
    bar += " and with an addition";
    TS_ASSERT_EQUALS(refStr.getData(), empty);
    TS_ASSERT_EQUALS(refStr2.getData(), bar);

    TS_ASSERT_EQUALS(backedStr.getData(), "baz");
    baz = "something else";
    TS_ASSERT_EQUALS(backedStr.getData(), "baz");

    TS_ASSERT_EQUALS(sInt.getData(), 10);
    sInt.setData(100);
    TS_ASSERT_EQUALS(sInt.getData(), 100);

    TS_ASSERT_EQUALS(sTimer.getData(), timespec());

    stringstream sstr;

    refStr.flushInformation(sstr);
    TS_ASSERT_EQUALS(sstr.str(), empty);
    sstr.str("");
    refStr2.flushInformation(sstr);
    TS_ASSERT_EQUALS(sstr.str(), bar);
    sstr.str("");
    backedStr.flushInformation(sstr);
    TS_ASSERT_EQUALS(sstr.str(), "baz");
    sstr.str("");
    sInt.flushInformation(sstr);
    TS_ASSERT_EQUALS(sstr.str(), "100");
    sstr.str("");
    sTimer.flushInformation(sstr);
    TS_ASSERT_EQUALS(sstr.str(), "0.00000000");

    sTimer.start();
    timespec zero = { 0, 0 };
    //TS_ASSERT_EQUALS(zero, sTimer.getData());
    sTimer.stop();
    TS_ASSERT_LESS_THAN(zero, sTimer.getData());
#endif /* CVC4_STATISTICS_ON */
  }

};
