/*********************                                                        */
/*! \file stats_histogram.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Histogram statistics
 **
 ** Stat classes that represent histograms
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATS_HISTOGRAM_H
#define CVC4__UTIL__STATS_HISTOGRAM_H

#include <map>
#include <vector>

#include "util/stats_base.h"

namespace CVC4 {

template <class T>
class HistogramStat : public Stat
{
 private:
  using Histogram = std::map<T, std::uint64_t>;
  Histogram d_hist;

 public:
  /** Construct a histogram of a stream of entries. */
  HistogramStat(const std::string& name) : Stat(name) {}

  void flushInformation(std::ostream& out) const override
  {
    auto i = d_hist.begin();
    auto end = d_hist.end();
    out << "[";
    while (i != end)
    {
      const T& key = (*i).first;
      std::uint64_t count = (*i).second;
      out << "(" << key << " : " << count << ")";
      ++i;
      if (i != end)
      {
        out << ", ";
      }
    }
    out << "]";
  }

  void safeFlushInformation(int fd) const override
  {
    auto i = d_hist.begin();
    auto end = d_hist.end();
    safe_print(fd, "[");
    while (i != end)
    {
      const T& key = (*i).first;
      std::uint64_t count = (*i).second;
      safe_print(fd, "(");
      safe_print<T>(fd, key);
      safe_print(fd, " : ");
      safe_print<uint64_t>(fd, count);
      safe_print(fd, ")");
      ++i;
      if (i != end)
      {
        safe_print(fd, ", ");
      }
    }
    safe_print(fd, "]");
  }

  HistogramStat& operator<<(const T& val)
  {
    if (CVC4_USE_STATISTICS)
    {
      if (d_hist.find(val) == d_hist.end())
      {
        d_hist.insert(std::make_pair(val, 0));
      }
      d_hist[val]++;
    }
    return (*this);
  }

}; /* class HistogramStat */

/**
 * A histogram statistic class for integral types.
 * Avoids using an std::map (like the generic HistogramStat) in favor of a
 * faster std::vector by casting the integral values to indices into the
 * vector. Requires the type to be an integral type that is convertible to
 * std::int64_t, also supporting appropriate enum types.
 * The vector is resized on demand to grow as necessary and supports negative
 * values as well.
 */
template <typename Integral>
class IntegralHistogramStat : public Stat
{
  static_assert(std::is_integral<Integral>::value
                    || std::is_enum<Integral>::value,
                "Type should be a fundamental integral type.");

 private:
  std::vector<std::uint64_t> d_hist;
  std::int64_t d_offset;

 public:
  /** Construct a histogram of a stream of entries. */
  IntegralHistogramStat(const std::string& name) : Stat(name) {}

  void flushInformation(std::ostream& out) const override
  {
    out << "[";
    bool first = true;
    for (std::size_t i = 0, n = d_hist.size(); i < n; ++i)
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
        out << "(" << static_cast<Integral>(i + d_offset) << " : "
            << d_hist[i] << ")";
      }
    }
    out << "]";
  }

  void safeFlushInformation(int fd) const override
  {
    safe_print(fd, "[");
    bool first = true;
    for (std::size_t i = 0, n = d_hist.size(); i < n; ++i)
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
        safe_print<std::uint64_t>(fd, d_hist[i]);
        safe_print(fd, ")");
      }
    }
    safe_print(fd, "]");
  }

  IntegralHistogramStat& operator<<(Integral val)
  {
    if (CVC4_USE_STATISTICS)
    {
      std::int64_t v = static_cast<std::int64_t>(val);
      if (d_hist.empty())
      {
        d_offset = v;
      }
      if (v < d_offset)
      {
        d_hist.insert(d_hist.begin(), d_offset - v, 0);
        d_offset = v;
      }
      if (static_cast<std::size_t>(v - d_offset) >= d_hist.size())
      {
        d_hist.resize(v - d_offset + 1);
      }
      d_hist[v - d_offset]++;
    }
    return (*this);
  }
}; /* class IntegralHistogramStat */

}  // namespace CVC4

#endif
