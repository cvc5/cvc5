/*********************                                                        */
/*! \file statistics_base.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Basic statistics representation
 **
 ** The basic statistics classes.
 **/

#include "util/statistics_stats.h"

#include "base/check.h"
#include "util/statistics_value.h"

namespace CVC4 {

AverageStat& AverageStat::operator<<(double v)
{
  if (CVC4_USE_STATISTICS)
  {
    d_data->d_sum += v;
    d_data->d_count++;
  }
  return *this;
}

IntStats& IntStats::operator=(int64_t val)
{
  if (CVC4_USE_STATISTICS)
  {
    d_data->d_value = val;
  }
  return *this;
}
IntStats& IntStats::operator++()
{
  if (CVC4_USE_STATISTICS)
  {
    d_data->d_value++;
  }
  return *this;
}
IntStats& IntStats::operator++(int)
{
  if (CVC4_USE_STATISTICS)
  {
    d_data->d_value++;
  }
  return *this;
}
IntStats& IntStats::operator+=(int64_t val)
{
  if (CVC4_USE_STATISTICS)
  {
    d_data->d_value += val;
  }
  return *this;
}
void IntStats::maxAssign(int64_t val)
{
  if (d_data->d_value < val)
  {
    d_data->d_value = val;
  }
}
void IntStats::minAssign(int64_t val)
{
  if (d_data->d_value > val)
  {
    d_data->d_value = val;
  }
}

void TimerStat::start()
{
  if (CVC4_USE_STATISTICS)
  {
    PrettyCheckArgument(!d_data->d_running, *this, "timer already running");
    d_data->d_start = StatisticTimerValue::clock::now();
    d_data->d_running = true;
  }
}
void TimerStat::stop()
{
  if (CVC4_USE_STATISTICS)
  {
    AlwaysAssert(d_data->d_running) << "timer not running";
    d_data->d_duration += StatisticTimerValue::clock::now() - d_data->d_start;
    d_data->d_running = false;
  }
}
bool TimerStat::running() const
{
  if (CVC4_USE_STATISTICS)
  {
    return d_data->d_running;
  }
  else
  {
    return false;
  }
}

CodeTimer::CodeTimer(TimerStat& timer, bool allow_reentrant)
    : d_timer(timer), d_reentrant(false)
{
  if (CVC4_USE_STATISTICS)
  {
    if (!allow_reentrant || !(d_reentrant = d_timer.running()))
    {
      d_timer.start();
    }
  }
}
CodeTimer::~CodeTimer()
{
  if (CVC4_USE_STATISTICS)
  {
    if (!d_reentrant)
    {
      d_timer.stop();
    }
  }
}

}  // namespace CVC4
