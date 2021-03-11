/*********************                                                        */
/*! \file stats_timer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Timer statistics
 **
 ** Stat classes that hold timers
 **/

#include "util/stats_timer.h"

#include <iostream>

#include "base/check.h"
#include "util/ostream_util.h"

namespace CVC4 {

template <>
void safe_print(int fd, const timer_stat_detail::duration& t)
{
  safe_print<uint64_t>(fd, t / std::chrono::seconds(1));
  safe_print(fd, ".");
  safe_print_right_aligned(fd, (t % std::chrono::seconds(1)).count(), 9);
}

void TimerStat::start()
{
  if (CVC4_USE_STATISTICS)
  {
    PrettyCheckArgument(!d_running, *this, "timer already running");
    d_start = timer_stat_detail::clock::now();
    d_running = true;
  }
}

void TimerStat::stop()
{
  if (CVC4_USE_STATISTICS)
  {
    AlwaysAssert(d_running) << "timer not running";
    d_data += timer_stat_detail::clock::now() - d_start;
    d_running = false;
  }
}

bool TimerStat::running() const { return d_running; }

timer_stat_detail::duration TimerStat::get() const
{
  auto data = d_data;
  if (CVC4_USE_STATISTICS && d_running)
  {
    data += timer_stat_detail::clock::now() - d_start;
  }
  return data;
}

SExpr TimerStat::getValue() const
{
  auto data = d_data;
  if (CVC4_USE_STATISTICS && d_running)
  {
    data += timer_stat_detail::clock::now() - d_start;
  }
  std::stringstream ss;
  ss << std::fixed << std::setprecision(8) << data;
  return SExpr(Rational::fromDecimal(ss.str()));
}

void TimerStat::flushInformation(std::ostream& out) const { out << get(); }

void TimerStat::safeFlushInformation(int fd) const
{
  // Overwrite the implementation in the superclass because we cannot use
  // getDataRef(): it might return stale data if the timer is currently
  // running.
  safe_print<timer_stat_detail::duration>(fd, get());
}

CodeTimer::CodeTimer(TimerStat& timer, bool allow_reentrant)
    : d_timer(timer), d_reentrant(false)
{
  if (!allow_reentrant || !(d_reentrant = d_timer.running()))
  {
    d_timer.start();
  }
}
CodeTimer::~CodeTimer()
{
  if (!d_reentrant)
  {
    d_timer.stop();
  }
}

}  // namespace CVC4
