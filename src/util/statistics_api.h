/*********************                                                        */
/*! \file statistics_api.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics representation for API
 **
 ** The Statistics object used in the API.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_API_H
#define CVC4__UTIL__STATISTICS_API_H

#include <iterator>
#include <map>
#include <string>
#include <variant>

namespace CVC4 {

class StatisticRegistry;

/**
 * Represents a single statistic value for the API.
 * A value is a variant of int64_t, double, std::string or a histogram
 * (std::map<std::string, uint64_t>).
 * Implements methods to check for the type (e.g. `isInt`, `isString`) and
 * return the value in a given type (e.g. `getInt`, `getString`).
 */
class StatViewer
{
 public:
  friend std::ostream& operator<<(std::ostream& os, const StatViewer& sv);
  /** Create from the given value. */
  template <typename T>
  StatViewer(bool expert, const T& t) : d_expert(expert), d_data(t)
  {
  }
  using HistogramData = std::map<std::string, uint64_t>;

  /** Is this value for experts only? */
  bool isExpert() const;

  /** Is this value an integer? */
  bool isInt() const;
  /** Return the integer value */
  int64_t getInt() const;
  /** Is this value a double? */
  bool isDouble() const;
  /** Return the double value */
  double getDouble() const;
  /** Is this value an string? */
  bool isString() const;
  /** Return the string value */
  std::string getString() const;
  /** Is this value an histogram? */
  bool isHistogram() const;
  /** Return the histogram value */
  const HistogramData& getHistogram() const;

 private:
  /** Whether this statistic is only meant for experts */
  bool d_expert;
  std::variant<int64_t, double, std::string, HistogramData> d_data;
};

std::ostream& operator<<(std::ostream& os, const StatViewer& sv);

/**
 * Represents the internally collected statistics, converted to `StatViewer`
 * objects. Supports querying for a statistic name and iteration.
 */
class Statistics
{
 public:
  // TODO: make this private and friend with SmtEngine
  Statistics(const StatisticRegistry& reg);
  /** Retrieve the statistic with the given name. */
  const StatViewer& get(const std::string& name);
  /** begin iteration */
  auto begin() const { return d_stats.begin(); }
  /** end iteration */
  auto end() const { return d_stats.end(); }

 private:
  std::map<std::string, StatViewer> d_stats;
};
std::ostream& operator<<(std::ostream& out, const Statistics& stats);

}  // namespace CVC4

#endif
