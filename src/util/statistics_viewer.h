/*********************                                                        */
/*! \file statistics_viewer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistic value representation for the API
 **
 ** Statistic value representation for the API.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_VIEWER_H
#define CVC4__UTIL__STATISTICS_VIEWER_H

#include <cassert>
#include <map>
#include <string>
#include <variant>

namespace CVC4 {

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
  StatViewer(const T& t) : d_data(t)
  {
  }
  using HistogramData = std::map<std::string, uint64_t>;

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
  std::variant<int64_t, double, std::string, HistogramData> d_data;
};

std::ostream& operator<<(std::ostream& os, const StatViewer& sv);

}  // namespace CVC4

#endif
