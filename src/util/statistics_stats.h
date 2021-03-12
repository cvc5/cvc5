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
 */

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_STATS_H
#define CVC4__UTIL__STATISTICS_STATS_H

#include <optional>

namespace CVC4 {

// forward declare all values to avoid inclusion
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

/**
 * Collects the average of a series of double values.
 * New values are added by
 *   AverageStat stat;
 *   stat << 1.0 << 2.0;
 */
class AverageStats
{
 public:
  /** Allow access to private constructor */
  friend class StatisticRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticAverageValue;
  /** Add the value `v` to the running average */
  AverageStats& operator<<(double v);

 private:
  AverageStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

/**
 * Collects a histogram over some type.
 * The type needs to be (convertible to) integral.
 * New values are added by
 *    HistogramStat<Kind> stat;
 *    stat << Kind::PLUS << Kind::AND;
 */
template <typename Integral>
class HistogramStats
{
 public:
  /** Allow access to private constructor */
  friend class StatisticRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticHistogramValue<Integral>;
  /** Add the value `val` to the histogram */
  HistogramStats& operator<<(Integral val)
  {
    d_data->add(val);
    return *this;
  }

 private:
  HistogramStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

/**
 * Stores an integer value as int64_t.
 * Supports the most useful standard operators (assignment, pre- and
 * post-increment, addition assignment) and some custom ones (maximum
 * assignment, minimum assignment).
 */
class IntStats
{
 public:
  /** Allow access to private constructor */
  friend class StatisticRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticBackedValue<int64_t>;
  /** Set the integer to `val` */
  IntStats& operator=(int64_t val);
  /** Pre-increment for the integer */
  IntStats& operator++();
  /** Post-increment for the integer */
  IntStats& operator++(int);
  /** Add `val` to the integer */
  IntStats& operator+=(int64_t val);
  /** Assign the maximum of the current value and `val` */
  void maxAssign(int64_t val);
  /** Assign the minimum of the current value and `val` */
  void minAssign(int64_t val);

 private:
  IntStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

/**
 * Stores the reference to some value that exists outside of this statistic.
 * Despite being called `ReferenceStat`, the reference is held as a pointer
 * and can thus be reset using `set`.
 * Note that the referenced object must have a lifetime that is longer than
 * the lifetime of the `ReferenceStat` object. Upon destruction of the
 * `ReferenceStat` the current value of the referenced object is copied into
 * the `StatisticRegistry`.
 *
 * To convert to the API representation in `StatViewer`, `T` can only be one
 * of the types listed in `StatViewer::d_data` (or be implicitly converted to
 * one of them).
 */
template <typename T>
class ReferenceStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticReferenceValue<T>;
  /** Reset the reference to point to `t`. */
  void set(const T& t) { d_data->d_value = &t; }
  /** Copy the current value of the referenced object. */
  ~ReferenceStat() { d_data->commit(); }

 private:
  ReferenceStat(StatisticReferenceValue<T>* data) : d_data(data) {}
  StatisticReferenceValue<T>* d_data;
};

/**
 * Stores the size of some container that exists outside of this statistic.
 * Note that the referenced container must have a lifetime that is longer than
 * the lifetime of the `SizeStat` object. Upon destruction of the `SizeStat`
 * the current size of the referenced container is copied into the
 * `StatisticRegistry`.
 */
template <typename T>
class SizeStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticSizeValue<T>;
  /** Reset the reference to point to `t`. */
  void set(const T& t) { d_data->d_value = &t; }
  /** Copy the current size of the referenced container. */
  ~SizeStat() { d_data->commit(); }

 private:
  SizeStat(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

class CodeTimers;
/**
 * Collects cumulative runtimes. The timer can be started and stopped
 * arbitrarily like a stopwatch. The value of the statistic is the
 * accumulated time over all (start,stop) pairs.
 *
 * Note that it is recommended to use it in an RAII fashion using the
 * `CodeTimers` class.
 */
class TimerStats
{
 public:
  /** Utility for RAII-style timing of code blocks */
  using CodeTimers = CVC4::CodeTimers;
  /** Allow access to private constructor */
  friend class StatisticRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticTimerValue;

  /** Start the timer. Assumes it is not already running. */
  void start();
  /** Stop the timer. Assumes it is running. */
  void stop();
  /** Checks whether the timer is running. */
  bool running() const;

 private:
  TimerStats(stat_type* data) : d_data(data) {}
  stat_type* d_data;
};

/**
 * Utility class to make it easier to call `stop`  at the end of a
 * code block. When constructed, it starts the timer. When
 * destructed, it stops the timer.
 *
 * Allows for reentrant usage. If `allow_reentrant` is true, we check
 * whether the timer is already running. If so, this particular instance
 * of `CodeTimer` neither starts nor stops the actual timer, but leaves
 * this to the first (or outermost) `CodeTimer`.
 */
class CodeTimers
{
 public:
  /** Disallow copying */
  CodeTimers(const CodeTimers& timer) = delete;
  /** Disallow assignment */
  CodeTimers& operator=(const CodeTimers& timer) = delete;
  /** Start the timer */
  CodeTimers(TimerStats& timer, bool allow_reentrant = false);
  /** Stop the timer */
  ~CodeTimers();

 private:
  TimerStats& d_timer;
  bool d_reentrant;
};

/**
 * Stores a simple value that can be set manually using regular assignment
 * or the `set` method.
 *
 * To convert to the API representation in `StatViewer`, `T` can only be one
 * of the types listed in `StatViewer::d_data` (or be implicitly converted to
 * one of them).
 */
template <typename T>
class ValueStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticRegistry;
  /** Set to `t` */
  void set(const T& t) { d_data->d_value = t; }
  /** Set to `t` */
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
