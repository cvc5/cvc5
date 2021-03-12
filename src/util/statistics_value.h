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
 ** \brief Basic statistics representation
 **
 ** The basic statistics classes.
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

#include "util/ostream_util.h"
#include "util/safe_print.h"
#include "util/statistics_viewer.h"

namespace CVC4 {

class StatisticRegistry;

class StatisticBaseValue
{
 public:
  virtual ~StatisticBaseValue() = default;
  virtual StatViewer getViewer() const = 0;
  virtual void print(std::ostream&) const = 0;
  virtual void print_safe(int fd) const = 0;
};
inline std::ostream& operator<<(std::ostream& out,
                                const StatisticBaseValue& sbv)
{
  sbv.print(out);
  return out;
}

struct StatisticAverageValue : StatisticBaseValue
{
  StatViewer getViewer() const override { return get(); }
  void print(std::ostream& out) const override { out << get(); }
  void print_safe(int fd) const override { safe_print<double>(fd, get()); }
  double get() const { return d_sum / d_count; }

  double d_sum;
  uint64_t d_count;
};

template <typename T>
struct StatisticBackedValue : StatisticBaseValue
{
  StatViewer getViewer() const override { return d_value; }
  void print(std::ostream& out) const override { out << d_value; }
  void print_safe(int fd) const override { safe_print<T>(fd, d_value); }

  T d_value;
};

/**
 * A histogram statistic class for integral types.
 * Avoids using an std::map (like the generic HistogramStat) in favor of a
 * faster std::vector by casting the integral values to indices into the
 * vector. Requires the type to be an integral type that is convertible to
 * int64_t, also supporting appropriate enum types.
 * The vector is resized on demand to grow as necessary and supports negative
 * values as well.
 */
template <typename Integral>
struct StatisticHistogramValue : StatisticBaseValue
{
  static_assert(std::is_integral<Integral>::value
                    || std::is_enum<Integral>::value,
                "Type should be a fundamental integral type.");

  StatViewer getViewer() const override
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
    return res;
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

  std::vector<uint64_t> d_hist;
  int64_t d_offset;
};

template <typename T>
struct StatisticReferenceValue : StatisticBaseValue
{
  StatViewer getViewer() const override { return get(); }
  void print(std::ostream& out) const override { out << get(); }
  void print_safe(int fd) const override { safe_print<T>(fd, get()); }
  void commit() { d_committed = *d_value; }
  const T& get() const { return d_committed ? *d_committed : *d_value; }

  const T* d_value = nullptr;
  std::optional<T> d_committed;
};

template <typename T>
struct StatisticSizeValue : StatisticBaseValue
{
  StatViewer getViewer() const override { return static_cast<int64_t>(get()); }
  void print(std::ostream& out) const override { out << get(); }
  void print_safe(int fd) const override { safe_print<size_t>(fd, get()); }
  void commit() { d_committed = d_value->size(); }
  size_t get() const { return d_committed ? *d_committed : d_value->size(); }

  const T* d_value = nullptr;
  std::optional<std::size_t> d_committed;
};

struct StatisticTimerValue : StatisticBaseValue
{
  using clock = std::chrono::steady_clock;
  using time_point = clock::time_point;
  struct duration : public std::chrono::nanoseconds
  {
  };
  StatViewer getViewer() const override { return static_cast<int64_t>(get() / std::chrono::milliseconds(1)); }
  void print(std::ostream& out) const override
  {
    StreamFormatScope format_scope(out);
    duration dur = get();

    out << (dur / std::chrono::seconds(1)) << "." << std::setfill('0')
              << std::setw(9) << std::right
              << (dur % std::chrono::seconds(1)).count();
  }
  void print_safe(int fd) const override
  {
    duration dur = get();
    safe_print<uint64_t>(fd, dur / std::chrono::seconds(1));
    safe_print(fd, ".");
    safe_print_right_aligned(fd, (dur % std::chrono::seconds(1)).count(), 9);
  }
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
