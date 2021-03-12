/*********************                                                        */
/*! \file statistics_api.cpp
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

#include "util/statistics_api.h"

#include "util/statistics_reg.h"
#include "util/statistics_value.h"
#include "util/statistics_viewer.h"

namespace CVC4 {

Statistics::Statistics(const StatisticRegistry& reg)
{
  for (const auto& svp : reg)
  {
    d_stats.emplace(svp.first, svp.second->getViewer());
  }
}

const StatViewer& Statistics::get(std::string name)
{
  auto it = d_stats.find(name);
  assert(it != d_stats.end());
  return it->second;
}

std::ostream& operator<<(std::ostream& out, const Statistics& stats)
{
  for (const auto& stat: stats)
  {
    out << stat.first << " = " << stat.second << std::endl;
  }
  return out;
}

}  // namespace CVC4
