/*********************                                                        */
/*! \file stats_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Aina Niemetz, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Stat and associated classes
 **
 ** Black box testing of CVC4::Stat and associated classes.
 **/

#include <fcntl.h>

#include <ctime>
#include <sstream>
#include <string>
#include <thread>

#include "expr/proof_rule.h"
#include "lib/clock_gettime.h"
#include "test.h"
#include "util/statistics_reg.h"
#include "util/statistics_stats.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& os, const StatisticBaseValue* sbv)
{
  sbv->print(os);
  return os;
}
bool operator==(const StatisticBaseValue* sbv, const std::string& s) {
  std::stringstream ss;
  ss << sbv;
  return ss.str() == s;
}

namespace test {

class TestUtilBlackStats : public TestInternal
{
};

TEST_F(TestUtilBlackStats, stats)
{
#ifdef CVC4_STATISTICS_ON
  StatisticRegistry reg(false);
  std::string empty, bar = "bar", baz = "baz";

  AverageStats avg = reg.registerAverage("avg");
  avg << 1.0 << 2.0;
  
  HistogramStats<int64_t> histInt = reg.registerHistogram<int64_t>("hist-int");
  histInt << 15 << 16 << 15 << 14 << 16;
  
  HistogramStats<PfRule> histPfRule = reg.registerHistogram<PfRule>("hist-pfrule");
  histPfRule << PfRule::ASSUME << PfRule::SCOPE << PfRule::ASSUME;

  IntStats intstat = reg.registerInt("int");
  intstat = 5;
  intstat++;

  ReferenceStats<std::string> refStr = reg.registerReference<std::string>("strref1", empty);
  ReferenceStats<std::string> refStr2 = reg.registerReference<std::string>("strref2", bar);

  TimerStats timer = reg.registerTimer("timer");
  {
    CodeTimers ct(timer);
    std::this_thread::sleep_for(std::chrono::milliseconds(50));
  }

  ValueStat<std::string> valStr = reg.registerValue("backed", baz);
  valStr.set("barz");
  ValueStat<double> valD1 = reg.registerValue("backedDouble", 16.5);
  valD1.set(3.5);
  ValueStat<double> valD2 = reg.registerValue("backedNegDouble", -16.5);
  valD2.set(-3.5);
  ValueStat<double> valD3 = reg.registerValue("backedDoubleNoDec", 2.0);
  valD3.set(17);

  ASSERT_EQ(reg.get("avg"), std::string("1.5"));
  ASSERT_EQ(reg.get("hist-int"), std::string("[(14 : 1), (15 : 2), (16 : 2)]"));
  ASSERT_EQ(reg.get("hist-pfrule"), std::string("[(ASSUME : 2), (SCOPE : 1)]"));
  ASSERT_EQ(reg.get("int"), std::string("6"));
  ASSERT_EQ(reg.get("strref1"), std::string(""));
  ASSERT_EQ(reg.get("strref2"), std::string("bar"));
  ASSERT_EQ(reg.get("backed"), std::string("barz"));
  ASSERT_EQ(reg.get("backedDouble"), std::string("3.5"));
  ASSERT_EQ(reg.get("backedNegDouble"), std::string("-3.5"));
  ASSERT_EQ(reg.get("backedDoubleNoDec"), std::string("17"));
/*
  ASSERT_EQ(refStr.getName(), "stat #1");
  ASSERT_EQ(refStr2.getName(), "refStr2");
  ASSERT_EQ(backedStr.getName(), "backed");
  ASSERT_EQ(sInt.getName(), "my int");
  ASSERT_EQ(sTimer.getName(), "a timer ! for measuring time");
  ASSERT_EQ(histIntStat.getName(), "hist-int");
  ASSERT_EQ(histPfRuleStat.getName(), "hist-pfrule");

  ASSERT_EQ(refStr.get(), empty);
  ASSERT_EQ(refStr2.get(), bar);
  empty = "a different string";
  bar += " and with an addition";
  ASSERT_EQ(refStr.get(), empty);
  ASSERT_EQ(refStr2.get(), bar);

  ASSERT_EQ(backedStr.get(), "baz");
  baz = "something else";
  ASSERT_EQ(backedStr.get(), "baz");

  ASSERT_EQ(sInt.get(), 10);
  sInt.set(100);
  ASSERT_EQ(sInt.get(), 100);

  ASSERT_TRUE(sTimer.get() == std::chrono::nanoseconds());

  std::stringstream sstr;

  refStr.flushInformation(sstr);
  ASSERT_EQ(sstr.str(), empty);
  sstr.str("");
  refStr2.flushInformation(sstr);
  ASSERT_EQ(sstr.str(), bar);
  sstr.str("");
  backedStr.flushInformation(sstr);
  ASSERT_EQ(sstr.str(), "baz");
  sstr.str("");
  sInt.flushInformation(sstr);
  ASSERT_EQ(sstr.str(), "100");
  sstr.str("");
  sTimer.flushInformation(sstr);
  ASSERT_EQ(sstr.str(), "0.000000000");

  // Test safeFlushInformation (and safe_print functions)
  char tmp_filename[] = "testXXXXXX";
  int fd = mkstemp(tmp_filename);
  ASSERT_NE(fd, -1);
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
  histIntStat.safeFlushInformation(fd);
  safe_print(fd, "\n");
  histPfRuleStat.safeFlushInformation(fd);
  safe_print(fd, "\n");
  backedUnsupported.safeFlushInformation(fd);
  off_t file_size = lseek(fd, 0, SEEK_CUR);
  close(fd);

  char* buf = new char[file_size];
  fd = open(tmp_filename, O_RDONLY);
  ASSERT_NE(fd, -1);
  ssize_t n_read = pread(fd, buf, file_size, 0);
  ASSERT_EQ(n_read, file_size);
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
      "[(14 : 1), (15 : 2), (16 : 2)]\n"
      "[(ASSUME : 2), (SCOPE : 1)]\n"
      "<unsupported>";
  ASSERT_EQ(strncmp(expected, buf, file_size), 0);
  delete[] buf;

  int ret = remove(tmp_filename);
  ASSERT_EQ(ret, 0);
*/
#endif
}
}  // namespace test
}  // namespace CVC4
