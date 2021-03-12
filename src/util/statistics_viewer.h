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
 ** \brief Statistics representation for API
 **
 ** Everything necessary to inspect and print statistics via the API.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_VIEWER_H
#define CVC4__UTIL__STATISTICS_VIEWER_H

#include <cassert>
#include <map>
#include <string>
#include <variant>

namespace CVC4 {

class StatViewer
{
 public:
 friend std::ostream& operator<<(std::ostream& os, const StatViewer& sv);
  template<typename T>
  StatViewer(const T& t): d_data(t) {}
  using HistogramData = std::map<std::string, uint64_t>;

  bool isInt() const;
  int64_t getInt() const;
  bool isDouble() const;
  double getDouble() const;
  bool isString() const;
  std::string getString() const;
  bool isHistogram() const;
  const HistogramData& getHistogram() const;

 private:
  std::variant<int64_t, double, std::string, HistogramData> d_data;
};

std::ostream& operator<<(std::ostream& os, const StatViewer& sv);

}  // namespace CVC4

#endif
