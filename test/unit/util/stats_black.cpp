/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::Stat and associated classes.
 */

#include <fcntl.h>

#include <ctime>
#include <sstream>
#include <string>
#include <thread>

#include "lib/clock_gettime.h"
#include "proof/proof_rule.h"
#include "test_env.h"
#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& os, const StatisticBaseValue* sbv)
{
  return os << *sbv;
}
bool operator==(const StatisticBaseValue* sbv, const std::string& s)
{
  std::stringstream ss;
  ss << sbv;
  return ss.str() == s;
}

namespace test {

class TestUtilBlackStats : public TestEnv
{
};

TEST_F(TestUtilBlackStats, stats)
{
#ifdef CVC5_STATISTICS_ON
  StatisticsRegistry reg(*d_env.get(), false);
  std::string empty, bar = "bar", baz = "baz";

  AverageStat avg = reg.registerAverage("avg");
  avg << 1.0 << 2.0;

  HistogramStat<int64_t> histInt = reg.registerHistogram<int64_t>("hist-int");
  histInt << 15 << 16 << 15 << 14 << 16;

  HistogramStat<PfRule> histPfRule =
      reg.registerHistogram<PfRule>("hist-pfrule");
  histPfRule << PfRule::ASSUME << PfRule::SCOPE << PfRule::ASSUME;

  IntStat intstat = reg.registerInt("int");
  intstat = 5;
  intstat++;

  ReferenceStat<std::string> refStr =
      reg.registerReference<std::string>("strref1", empty);
  ReferenceStat<std::string> refStr2 =
      reg.registerReference<std::string>("strref2", bar);

  TimerStat timer = reg.registerTimer("timer");
  {
    CodeTimer ct(timer);
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
  ASSERT_EQ(reg.get("hist-int"), std::string("{ 14: 1, 15: 2, 16: 2 }"));
  ASSERT_EQ(reg.get("hist-pfrule"), std::string("{ ASSUME: 2, SCOPE: 1 }"));
  ASSERT_EQ(reg.get("int"), std::string("6"));
  ASSERT_EQ(reg.get("strref1"), std::string(""));
  ASSERT_EQ(reg.get("strref2"), std::string("bar"));
  ASSERT_EQ(reg.get("backed"), std::string("barz"));
  ASSERT_EQ(reg.get("backedDouble"), std::string("3.5"));
  ASSERT_EQ(reg.get("backedNegDouble"), std::string("-3.5"));
  ASSERT_EQ(reg.get("backedDoubleNoDec"), std::string("17"));
#endif
}
}  // namespace test
}  // namespace cvc5::internal
