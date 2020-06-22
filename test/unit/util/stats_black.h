/*********************                                                        */
/*! \file stats_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Stat and associated classes
 **
 ** Black box testing of CVC4::Stat and associated classes.
 **/

#include <cxxtest/TestSuite.h>
#include <fcntl.h>
#include <ctime>
#include <sstream>
#include <string>

#include "lib/clock_gettime.h"
#include "util/statistics_registry.h"

using namespace CVC4;
using namespace std;

/**
 * This is a duplicate of operator== in statistics_registry.h.
 * This is duplicated here to try to avoid polluting top namepsace.
 *
 * If operator== is in the CVC4 namespace, there are some circumstances
 * where clang does not find this operator.
 */
bool operator==(const timespec& a, const timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec == b.tv_sec && a.tv_nsec == b.tv_nsec;
}

class StatsBlack : public CxxTest::TestSuite {
public:

  void testStats() {
#ifdef CVC4_STATISTICS_ON
    // StatisticsRegistry
    //static void flushStatistics(std::ostream& out);

    // static inline void registerStat(Stat* s);
    // static inline void unregisterStat(Stat* s);

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

    BackedStat<double> backedDouble("backedDouble", 16.5);
    BackedStat<double> backedNegDouble("backedNegDouble", -16.5);
    BackedStat<double> backedDoubleNoDec("backedDoubleNoDec", 2.0);
    BackedStat<bool> backedBool("backedBool", true);
    BackedStat<void*> backedAddr("backedDouble", (void*)0xDEADBEEF);
    HistogramStat<int64_t> histStat("hist");
    histStat << 5;
    histStat << 6;
    histStat << 5;
    histStat << 10;
    histStat << 10;
    histStat << 0;

    // A statistic with no safe_print support
    BackedStat<string*> backedUnsupported("backedUnsupported", &bar);

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
    TS_ASSERT_EQUALS(sstr.str(), "0.000000000");

    // Test safeFlushInformation (and safe_print functions)
    char tmp_filename[] = "testXXXXXX";
    int fd = mkstemp(tmp_filename);
    TS_ASSERT_DIFFERS(fd, -1);
    refStr.safeFlushInformation(fd);
    safe_print(fd, "\n");
    refStr2.safeFlushInformation(fd);
    safe_print(fd, "\n");
    backedStr.safeFlushInformation(fd);
    safe_print(fd, "\n");
    sInt.safeFlushInformation(fd);
    safe_print(fd, "\n");
    sTimer.safeFlushInformation(fd);
    safe_print(fd, "\n");
    backedDouble.safeFlushInformation(fd);
    safe_print(fd, "\n");
    backedNegDouble.safeFlushInformation(fd);
    safe_print(fd, "\n");
    backedDoubleNoDec.safeFlushInformation(fd);
    safe_print(fd, "\n");
    backedAddr.safeFlushInformation(fd);
    safe_print(fd, "\n");
    backedBool.safeFlushInformation(fd);
    safe_print(fd, "\n");
    histStat.safeFlushInformation(fd);
    safe_print(fd, "\n");
    backedUnsupported.safeFlushInformation(fd);
    off_t file_size = lseek(fd, 0, SEEK_CUR);
    close(fd);

    char* buf = new char[file_size];
    fd = open(tmp_filename, O_RDONLY);
    TS_ASSERT_DIFFERS(fd, -1);
    ssize_t n_read = pread(fd, buf, file_size, 0);
    TS_ASSERT_EQUALS(n_read, file_size);
    close(fd);

    const char* expected =
        "a different string\n"
        "bar and with an addition\n"
        "baz\n"
        "100\n"
        "0.000000000\n"
        "16.5\n"
        "-16.5\n"
        "2.0\n"
        "0xdeadbeef\n"
        "true\n"
        "[(0 : 1), (5 : 2), (6 : 1), (10 : 2)]\n"
        "<unsupported>";
    TS_ASSERT(strncmp(expected, buf, file_size) == 0);
    delete[] buf;

    int ret = remove(tmp_filename);
    TS_ASSERT_EQUALS(ret, 0);
#endif /* CVC4_STATISTICS_ON */
  }

};
