/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Matthew Sotoudeh, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistic proxy objects
 *
 * Conceptually, every statistic consists of a data object and a proxy
 * object. The proxy objects are issued by the `StatisticsRegistry` and
 * maintained by the user. They only hold a pointer to a matching data
 * object. The purpose of proxy objects is to implement methods to easily
 * change the statistic data, but shield the regular user from the internals.
 */

#include "cvc5_private_library.h"

#ifndef CVC5__UTIL__STATISTICS_STATS_H
#define CVC5__UTIL__STATISTICS_STATS_H

#include <optional>

#include "base/configuration.h"

namespace cvc5::internal {

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

class StatisticsRegistry;

/**
 * Collects the average of a series of double values.
 * New values are added by
 *   AverageStat stat;
 *   stat << 1.0 << 2.0;
 */
class AverageStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticsRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticAverageValue;
  /** Add the value `v` to the running average */
  AverageStat& operator<<(double v);

 private:
  /** Construct from a pointer to the internal data */
  AverageStat(stat_type* data) : d_data(data) {}
  /** The actual data that lives in the registry */
  stat_type* d_data;
};

/**
 * Collects a histogram over some type.
 * The type needs to be (convertible to) integral and support streaming to
 * an `std::ostream`.
 * New values are added by
 *    HistogramStat<Kind> stat;
 *    stat << Kind::ADD << Kind::AND;
 */
template <typename Integral>
class HistogramStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticsRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticHistogramValue<Integral>;
  /** Add the value `val` to the histogram */
  HistogramStat& operator<<(Integral val)
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      d_data->add(val);
    }
    return *this;
  }

 private:
  /** Construct from a pointer to the internal data */
  HistogramStat(stat_type* data) : d_data(data) {}
  /** The actual data that lives in the registry */
  stat_type* d_data;
};

/**
 * Stores the reference to some value that exists outside of this statistic.
 * Despite being called `ReferenceStat`, the reference is held as a pointer
 * and can thus be reset using `set`.
 * Note that the referenced object must have a lifetime that is longer than
 * the lifetime of the `ReferenceStat` object. Upon destruction of the
 * `ReferenceStat` the current value of the referenced object is copied into
 * the `StatisticsRegistry`.
 *
 * To convert to the API representation in `cvc5::Stat`, `T` can only be one
 * of the types accepted by the `cvc5::Stat` constructors (or be implicitly
 * converted to one of them).
 */
template <typename T>
class ReferenceStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticsRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticReferenceValue<T>;
  /** Reset the reference to point to `t`. */
  template <typename TT>
  void set(const TT& t)
  {
    static_assert(std::is_same_v<T, TT>, "Incorrect type for ReferenceStat");
    if constexpr (configuration::isStatisticsBuild())
    {
      d_data->d_value = &t;
    }
  }
  /** Commit the value currently pointed to and release it. */
  void reset()
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      d_data->commit();
      d_data->d_value = nullptr;
    }
  }
  /** Copy the current value of the referenced object. */
  ~ReferenceStat()
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      d_data->commit();
    }
  }

 private:
  /** Construct from a pointer to the internal data */
  ReferenceStat(StatisticReferenceValue<T>* data) : d_data(data) {}
  /** The actual data that lives in the registry */
  StatisticReferenceValue<T>* d_data;
};

/**
 * Stores the size of some container that exists outside of this statistic.
 * Note that the referenced container must have a lifetime that is longer than
 * the lifetime of the `SizeStat` object. Upon destruction of the `SizeStat`
 * the current size of the referenced container is copied into the
 * `StatisticsRegistry`.
 */
template <typename T>
class SizeStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticsRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticSizeValue<T>;
  /** Reset the reference to point to `t`. */
  void set(const T& t)
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      d_data->d_value = &t;
    }
  }
  /** Copy the current size of the referenced container. */
  ~SizeStat()
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      d_data->commit();
    }
  }

 private:
  /** Construct from a pointer to the internal data */
  SizeStat(stat_type* data) : d_data(data) {}
  /** The actual data that lives in the registry */
  stat_type* d_data;
};

class CodeTimer;
/**
 * Collects cumulative runtimes. The timer can be started and stopped
 * arbitrarily like a stopwatch. The value of the statistic is the
 * accumulated time over all (start,stop) pairs.
 * While the runtimes are stored in nanosecond precision internally,
 * the API exports runtimes as integral numbers in millisecond
 * precision.
 *
 * Note that it is recommended to use it in an RAII fashion using the
 * `CodeTimer` class.
 */
class TimerStat
{
 public:
  /** Utility for RAII-style timing of code blocks */
  using CodeTimer = cvc5::internal::CodeTimer;
  /** Allow access to private constructor */
  friend class StatisticsRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticTimerValue;

  /** Start the timer. Assumes it is not already running. */
  void start();
  /** Stop the timer. Assumes it is running. */
  void stop();
  /** Checks whether the timer is running. */
  bool running() const;

 private:
  /** Construct from a pointer to the internal data */
  TimerStat(stat_type* data) : d_data(data) {}
  /** The actual data that lives in the registry */
  stat_type* d_data;
};

/**
 * Utility class to make it easier to call `stop` at the end of a code
 * block. When constructed, it starts the timer. When destructed, it stops
 * the timer.
 *
 * Allows for reentrant usage. If `allow_reentrant` is true, we check
 * whether the timer is already running. If so, this particular instance
 * of `CodeTimer` neither starts nor stops the actual timer, but leaves
 * this to the first (or outermost) `CodeTimer`.
 */
class CodeTimer
{
 public:
  /** Disallow copying */
  CodeTimer(const CodeTimer& timer) = delete;
  /** Disallow assignment */
  CodeTimer& operator=(const CodeTimer& timer) = delete;
  /**
   * Start the timer.
   * If `allow_reentrant` is true we check whether the timer is already
   * running. If so, this particular instance of `CodeTimer` neither starts
   * nor stops the actual timer, but leaves this to the first (or outermost)
   * `CodeTimer`.
   */
  CodeTimer(TimerStat& timer, bool allow_reentrant = false);
  /** Stop the timer */
  ~CodeTimer();

 private:
  /** Reference to the timer this utility works on */
  TimerStat& d_timer;
  /** Whether this timer is reentrant (i.e. does not do anything) */
  bool d_reentrant;
};

/**
 * Stores a simple value that can be set manually using regular assignment
 * or the `set` method.
 *
 * To convert to the API representation in `cvc5::Stat`, `T` can only be one
 * of the types accepted by the `cvc5::Stat` constructors (or be implicitly
 * converted to one of them).
 */
template <typename T>
class ValueStat
{
 public:
  /** Allow access to private constructor */
  friend class StatisticsRegistry;
  friend class IntStat;
  /** Value stored for this statistic */
  using stat_type = StatisticBackedValue<T>;
  /** Set to `t` */
  void set(const T& t)
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      d_data->d_value = t;
    }
  }
  /** Set to `t` */
  ValueStat<T>& operator=(const T& t)
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      set(t);
    }
    return *this;
  }
  T get() const
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      return d_data->d_value;
    }
    return T();
  }

 private:
  /** Construct from a pointer to the internal data */
  ValueStat(StatisticBackedValue<T>* data) : d_data(data) {}
  /** The actual data that lives in the registry */
  StatisticBackedValue<T>* d_data;
};

/**
 * Stores an integer value as int64_t.
 * Supports the most useful standard operators (assignment, pre- and
 * post-increment, addition assignment) and some custom ones (maximum
 * assignment, minimum assignment).
 */
class IntStat : public ValueStat<int64_t>
{
 public:
  /** Allow access to private constructor */
  friend class StatisticsRegistry;
  /** Value stored for this statistic */
  using stat_type = StatisticBackedValue<int64_t>;
  /** Set to given value */
  IntStat& operator=(int64_t val);
  /** Pre-increment for the integer */
  IntStat& operator++();
  /** Post-increment for the integer */
  IntStat& operator++(int);
  /** Add `val` to the integer */
  IntStat& operator+=(int64_t val);
  /** Assign the maximum of the current value and `val` */
  void maxAssign(int64_t val);
  /** Assign the minimum of the current value and `val` */
  void minAssign(int64_t val);

 private:
  /** Construct from a pointer to the internal data */
  IntStat(stat_type* data) : ValueStat(data) {}
};

}  // namespace cvc5::internal

#endif
