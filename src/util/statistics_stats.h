/*********************                                                        */
/*! \file statistics_base.h
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

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_STATS_H
#define CVC4__UTIL__STATISTICS_STATS_H

#include <optional>

namespace CVC4 {

struct StatisticAverageValue;
template <typename T>
struct StatisticBackedValue;
template <typename T>
struct StatisticHistogramValue;
template <typename T>
struct StatisticReferenceValue;
template <typename T>
struct StatisticSizeValue;
struct StatisticTimerValue;

class StatisticRegistry;

class AverageStats
{
 public:
  friend class StatisticRegistry;
  using stat_type = StatisticAverageValue;
  AverageStats& operator<<(double v);

 private:
  AverageStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

template <typename Integral>
class HistogramStats
{
 public:
  friend class StatisticRegistry;
  using stat_type = StatisticHistogramValue<Integral>;
  HistogramStats& operator<<(Integral val)
  {
    d_data->add(val);
    return *this;
  }

 private:
  HistogramStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

class IntStats
{
 public:
  friend class StatisticRegistry;
  using stat_type = StatisticBackedValue<int64_t>;
  IntStats& operator++();
  IntStats& operator++(int);
  IntStats& operator+=(int64_t val);
  void maxAssign(int64_t val);
  void minAssign(int64_t val);

 private:
  IntStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

template <typename T>
class ReferenceStat
{
 public:
  friend class StatisticRegistry;
  using stat_type = StatisticReferenceValue<T>;
  void set(const T& t) { d_data->d_value = &t; }
  ~ReferenceStat() { d_data->commit(); }

 private:
  ReferenceStat(StatisticReferenceValue<T>* data) : d_data(data) {}
  StatisticReferenceValue<T>* d_data;
};

template <typename T>
class SizeStat
{
 public:
  friend class StatisticRegistry;
  using stat_type = StatisticSizeValue<T>;
  void set(const T& t) { d_data->d_value = &t; }
  ~SizeStat() { d_data->commit(); }

 private:
  SizeStat(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

class CodeTimers;
class TimerStats
{
  using CodeTimers = CVC4::CodeTimers;

 public:
  friend class StatisticRegistry;
  using stat_type = StatisticTimerValue;

  void start();
  void stop();
  bool running() const;

 private:
  TimerStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

/**
 * Utility class to make it easier to call stop() at the end of a
 * code block.  When constructed, it starts the timer.  When
 * destructed, it stops the timer.
 */
class CodeTimers
{
 public:
  CodeTimers(TimerStats& timer, bool allow_reentrant = false);
  ~CodeTimers();

 private:
  TimerStats& d_timer;
  bool d_reentrant;

  /** Private copy constructor undefined (no copy permitted). */
  CodeTimers(const CodeTimers& timer) = delete;
  /** Private assignment operator undefined (no copy permitted). */
  CodeTimers& operator=(const CodeTimers& timer) = delete;
}; /* class CodeTimer */

template <typename T>
class ValueStat
{
 public:
  friend class StatisticRegistry;
  void set(const T& t) { d_data->d_value = t; }
  ValueStat<T>& operator=(const T& t)
  {
    set(t);
    return *this;
  }

 private:
  ValueStat(StatisticBackedValue<T>* data) : d_data(data) {}
  StatisticBackedValue<T>* d_data;
};

}  // namespace CVC4

#endif
