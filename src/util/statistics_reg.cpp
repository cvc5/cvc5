/*********************                                                        */
/*! \file statistics_reg.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Central statistics registry.
 **
 ** The StatisticsRegistry that issues statistic proxy objects.
 **/

#include "util/statistics_reg.h"

#include "util/statistics_public.h"

namespace CVC4 {

StatisticRegistry::StatisticRegistry() {
  register_public_statistics(*this);
}

std::ostream& operator<<(std::ostream& os, const StatisticRegistry& sr)
{
  for (const auto& s : sr.d_stats)
  {
    os << s.first << " = " << *s.second << std::endl;
  }
  return os;
}

}  // namespace CVC4
