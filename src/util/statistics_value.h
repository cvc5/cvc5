/*********************                                                        */
/*! \file statistics_value.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistic data classes
 **
 ** The statistic data classes that actually hold the data for the statistics.
 **
 ** Conceptually, every statistic consists of a data object and a proxy object.
 ** The data objects (statistic values) are derived from `StatisticBaseValue`
 ** and live in the `StatisticRegistry`.
 ** They are solely exported to the proxy objects, which should be the sole
 ** way to manipulate the data of a data object.
 ** The data objects themselves need to implement printing (normal and safe) and
 ** conversion to the API type `Stat`.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_VALUE_H
#define CVC4__UTIL__STATISTICS_VALUE_H

#include <chrono>
#include <iomanip>
#include <map>
#include <optional>
#include <sstream>
#include <vector>

#include "api/cvc4cpp.h"
#include "util/ostream_util.h"
#include "util/safe_print.h"

namespace CVC4 {

class StatisticRegistry;

/**
 * Base class for all statistic values.
 * Requires three methods:
 * - `getViewer` converts to the API representation `Stat`
 * - `print` writes the data to a regular `std::ostream`
 * - `print_safe` safely writes the data to a file descriptor
 */
struct StatisticBaseValue
{
  virtual ~StatisticBaseValue() = default;
  virtual api::Stat getViewer() const = 0;
  virtual void print(std::ostream&) const = 0;
  virtual void print_safe(int fd) const = 0;

  bool d_expert = true;
};
/** Writes the data to an output stream */
inline std::ostream& operator<<(std::ostream& out,
                                const StatisticBaseValue& sbv)
{
  sbv.print(out);
  return out;
}

/** Holds the data for an running average statistic */
struct StatisticAverageValue : StatisticBaseValue
{
  api::Stat getViewer() const override { return api::Stat(d_expert, get()); }
  void print(std::ostream& out) const override { out << get(); }
  void print_safe(int fd) const override { safe_print<double>(fd, get()); }
  double get() const { return d_sum / d_count; }

  /** Sum of added values */
  double d_sum;
  /** Number of added values */
  uint64_t d_count;
};

/**
 * Holds some value of type `T`.
 *
 * To convert to the API representation in `getViewer`, `T` can only be one
 * of the types listed in `Stat::d_data` (or be implicitly converted to
 * one of them).
 */
template <typename T>
struct StatisticBackedValue : StatisticBaseValue
{
  api::Stat getViewer() const override
  {
    return api::Stat(d_expert, d_value);
  }
  void print(std::ostream& out) const override { out << d_value; }
  void print_safe(int fd) const override { safe_print<T>(fd, d_value); }

  T d_value;
};

/**
 * Holds the data for a histogram. We assume the type to be (convertible to)
 * integral, and we can thus use a std::vector<uint64_t> for fast storage.
 * The core idea is to track the minimum and maximum values `[a,b]` that have
 * been added to the histogram and maintain a vector with `b-a+1` values.
 * The vector is resized on demand to grow as necessary and supports negative
 * values as well.
 * Note that the template type needs to have a streaming operator to convert it
 * to a string in `getViewer`.
 */
template <typename Integral>
struct StatisticHistogramValue : StatisticBaseValue
{
  static_assert(std::is_integral<Integral>::value
                    || std::is_enum<Integral>::value,
                "Type should be a fundamental integral type.");

  /**
   * Convert the internal representation to a `std::map<std::string, uint64_t>`
   */
  api::Stat getViewer() const override
  {
    std::map<std::string, uint64_t> res;
    for (size_t i = 0, n = d_hist.size(); i < n; ++i)
    {
      if (d_hist[i] > 0)
      {
        std::stringstream ss;
        ss << static_cast<Integral>(i + d_offset);
        res.emplace(ss.str(), d_hist[i]);
      }
    }
    return api::Stat(d_expert, res);
  }
  void print(std::ostream& out) const override
  {
    out << "[";
    bool first = true;
    for (size_t i = 0, n = d_hist.size(); i < n; ++i)
    {
      if (d_hist[i] > 0)
      {
        if (first)
        {
          first = false;
        }
        else
        {
          out << ", ";
        }
        out << "(" << static_cast<Integral>(i + d_offset) << " : " << d_hist[i]
            << ")";
      }
    }
    out << "]";
  }
  void print_safe(int fd) const override
  {
    safe_print(fd, "[");
    bool first = true;
    for (size_t i = 0, n = d_hist.size(); i < n; ++i)
    {
      if (d_hist[i] > 0)
      {
        if (first)
        {
          first = false;
        }
        else
        {
          safe_print(fd, ", ");
        }
        safe_print(fd, "(");
        safe_print<Integral>(fd, static_cast<Integral>(i + d_offset));
        safe_print(fd, " : ");
        safe_print<uint64_t>(fd, d_hist[i]);
        safe_print(fd, ")");
      }
    }
    safe_print(fd, "]");
  }

  /**
   * Add `val` to the histogram. Casts `val` to `int64_t`, then resizes and
   * moves the vector entries as necessary.
   */
  void add(Integral val)
  {
    int64_t v = static_cast<int64_t>(val);
    if (d_hist.empty())
    {
      d_offset = v;
    }
    if (v < d_offset)
    {
      d_hist.insert(d_hist.begin(), d_offset - v, 0);
      d_offset = v;
    }
    if (static_cast<size_t>(v - d_offset) >= d_hist.size())
    {
      d_hist.resize(v - d_offset + 1);
    }
    d_hist[v - d_offset]++;
  }

  /** Actual data */
  std::vector<uint64_t> d_hist;
  /** Offset of the entries. d_hist[i] corresponds to Interval(d_offset + i) */
  int64_t d_offset;
};

/**
 * Holds the data for a `ReferenceStat`.
 * When the `ReferenceStat` is destroyed the current values is copied into
 * `d_committed`. Once `d_committed` is set, this value is returned, even if
 * the reference is still valid.
 */
template <typename T>
struct StatisticReferenceValue : StatisticBaseValue
{
  api::Stat getViewer() const override { return api::Stat(d_expert, get()); }
  void print(std::ostream& out) const override { out << get(); }
  void print_safe(int fd) const override { safe_print<T>(fd, get()); }
  void commit() { d_committed = *d_value; }
  const T& get() const { return d_committed ? *d_committed : *d_value; }

  const T* d_value = nullptr;
  std::optional<T> d_committed;
};

/**
 * Holds the data for a `SizeStat`.
 * When the `SizeStat` is destroyed the current size is copied into
 * `d_committed`. Once `d_committed` is set, this value is returned, even if
 * the reference is still valid.
 */
template <typename T>
struct StatisticSizeValue : StatisticBaseValue
{
  api::Stat getViewer() const override
  {
    return api::Stat(d_expert, static_cast<int64_t>(get()));
  }
  void print(std::ostream& out) const override { out << get(); }
  void print_safe(int fd) const override { safe_print<size_t>(fd, get()); }
  void commit() { d_committed = d_value->size(); }
  size_t get() const { return d_committed ? *d_committed : d_value->size(); }

  const T* d_value = nullptr;
  std::optional<std::size_t> d_committed;
};

/**
 * Holds the data for a `TimerStat`.
 * Uses `std::chrono` to obtain the current time, store a time point and sum up
 * the total durations.
 */
struct StatisticTimerValue : StatisticBaseValue
{
  using clock = std::chrono::steady_clock;
  using time_point = clock::time_point;
  struct duration : public std::chrono::nanoseconds
  {
  };
  /** Returns the number of milliseconds */
  api::Stat getViewer() const override
  {
    return api::Stat(
        d_expert, static_cast<int64_t>(get() / std::chrono::milliseconds(1)));
  }
  /** Prints seconds in fixed-point format */
  void print(std::ostream& out) const override
  {
    StreamFormatScope format_scope(out);
    duration dur = get();

    out << (dur / std::chrono::seconds(1)) << "." << std::setfill('0')
        << std::setw(9) << std::right
        << (dur % std::chrono::seconds(1)).count();
  }
  /** Prints seconds in fixed-point format */
  void print_safe(int fd) const override
  {
    duration dur = get();
    safe_print<uint64_t>(fd, dur / std::chrono::seconds(1));
    safe_print(fd, ".");
    safe_print_right_aligned(fd, (dur % std::chrono::seconds(1)).count(), 9);
  }
  /** Make sure that we include the time of a currently running timer */
  duration get() const
  {
    auto data = d_duration;
    if (d_running)
    {
      data += clock::now() - d_start;
    }
    return data;
  }

  duration d_duration;
  time_point d_start;
  bool d_running;
};

}  // namespace CVC4

#endif
