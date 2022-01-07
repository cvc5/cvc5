/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Basic statistics representation.
 */

#include "util/statistics_stats.h"

#include "base/check.h"
#include "util/statistics_value.h"

namespace cvc5 {

AverageStat& AverageStat::operator<<(double v)
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    d_data->d_sum += v;
    d_data->d_count++;
  }
  return *this;
}

IntStat& IntStat::operator=(int64_t val)
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    d_data->d_value = val;
  }
  return *this;
}

IntStat& IntStat::operator++()
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    d_data->d_value++;
  }
  return *this;
}

IntStat& IntStat::operator++(int)
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    d_data->d_value++;
  }
  return *this;
}

IntStat& IntStat::operator+=(int64_t val)
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    d_data->d_value += val;
  }
  return *this;
}

void IntStat::maxAssign(int64_t val)
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    if (d_data->d_value < val)
    {
      d_data->d_value = val;
    }
  }
}

void IntStat::minAssign(int64_t val)
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    if (d_data->d_value > val)
    {
      d_data->d_value = val;
    }
  }
}

void TimerStat::start()
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    Assert(!d_data->d_running) << "timer is already running";
    d_data->d_start = StatisticTimerValue::clock::now();
    d_data->d_running = true;
  }
}
void TimerStat::stop()
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    Assert(d_data->d_running) << "timer is not running";
    d_data->d_duration += StatisticTimerValue::clock::now() - d_data->d_start;
    d_data->d_running = false;
  }
}
bool TimerStat::running() const
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    return d_data->d_running;
  }
  return false;
}

CodeTimer::CodeTimer(TimerStat& timer, bool allow_reentrant)
    : d_timer(timer), d_reentrant(false)
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    if (!allow_reentrant || !(d_reentrant = d_timer.running()))
    {
      d_timer.start();
    }
  }
}
CodeTimer::~CodeTimer()
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    if (!d_reentrant)
    {
      d_timer.stop();
    }
  }
}

}  // namespace cvc5
