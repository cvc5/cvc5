/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Regression test for ResourceManager::getRemainingTime() uint64_t underflow.
 *
 * `getRemainingTime()` returns
 *   `perCallMillisecondLimit - d_perCallTimer.elapsed()`
 * with both operands `uint64_t`. Once the per-call wall-clock timer overruns
 * the limit, the subtraction wraps to a value close to 2^64. Callers consume
 * this as either a huge double (cryptominisat, cocoa_util) or as a "remaining"
 * value, silently passing the deadline.
 *
 * The test pokes `WallClockTimer`'s internal time points directly via the
 * white-box build (`-fno-access-control`) instead of sleeping, so the timer
 * deterministically reports a 1 s overrun against the 5 ms limit. Sleep-based
 * tests against `WallClockTimer::clock` (a `std::chrono::system_clock`) are
 * vulnerable to NTP rewinds on CI VMs.
 */

#include <chrono>

#include "options/base_options.h"
#include "options/options.h"
#include "test.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace test {

class TestResourceManagerWhite : public TestInternal
{
};

TEST_F(TestResourceManagerWhite, RemainingTimeSaturatesOnOverrun)
{
  Options options;
  options.write_base().perCallMillisecondLimit = 5;
  StatisticsRegistry stats;
  ResourceManager rm(stats, options);

  rm.beginCall();

  // White-box: rewind the per-call timer's start so `elapsed()` returns
  // ~1000 ms regardless of wall-clock progress.
  using timer_time_point = decltype(rm.d_perCallTimer.d_start);
  auto now = timer_time_point::clock::now();
  rm.d_perCallTimer.d_start = now - std::chrono::milliseconds(1000);

  // Pre-fix: huge value (~2^64). Post-fix: 0.
  EXPECT_EQ(rm.getRemainingTime(), 0);
}

}  // namespace test
}  // namespace cvc5::internal
