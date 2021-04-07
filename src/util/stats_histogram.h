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

namespace cvc5 {

/**
 * A histogram statistic class for integral types.
 * Avoids using an std::map (like we would do for generic types) in favor of a
 * faster std::vector by casting the integral values to indices into the
 * vector. Requires the type to be an integral type that is convertible to
 * int64_t, also supporting appropriate enum types.
 * The vector is resized on demand to grow as necessary and supports negative
 * values as well.
 */
template <typename Integral>
class IntegralHistogramStat : public Stat
{
  static_assert(std::is_integral<Integral>::value
                    || std::is_enum<Integral>::value,
                "Type should be a fundamental integral type.");

 public:
  /** Construct a histogram of a stream of entries. */
  IntegralHistogramStat(const std::string& name) : Stat(name) {}

  void flushInformation(std::ostream& out) const override
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

  IntegralHistogramStat& operator<<(Integral val)
  {
    if (CVC4_USE_STATISTICS)
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
    return (*this);
  }

 private:
  std::vector<uint64_t> d_hist;
  int64_t d_offset;
}; /* class IntegralHistogramStat */

}  // namespace cvc5

#endif
