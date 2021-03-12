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

#include <map>
#include <string>

#include "util/statistics_viewer.h"

namespace CVC4 {

class StatisticRegistry;

class Statistics
{
 public:
  // TODO: make this private and friend with SmtEngine
  Statistics(const StatisticRegistry& reg);
  const StatViewer& get(std::string name);
  auto begin() const { return d_stats.begin(); }
  auto end() const { return d_stats.end(); }

 private:
  std::map<std::string, StatViewer> d_stats;
};
std::ostream& operator<<(std::ostream& out, const Statistics& stats);

}  // namespace CVC4

#endif
