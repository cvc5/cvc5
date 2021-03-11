/*********************                                                        */
/*! \file statistics_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/statistics_registry.h"

#include <cstdlib>
#include <iostream>

#include "base/check.h"
#include "lib/clock_gettime.h"
#include "util/ostream_util.h"

#ifdef CVC4_STATISTICS_ON
#  define CVC4_USE_STATISTICS true
#else
#  define CVC4_USE_STATISTICS false
#endif


/****************************************************************************/
/* Some utility functions for timespec                                    */
/****************************************************************************/
namespace CVC4 {

void StatisticsRegistry::registerStat(Stat* s)
{
#ifdef CVC4_STATISTICS_ON
  PrettyCheckArgument(
      d_stats.find(s) == d_stats.end(),
      s,
      "Statistic `%s' is already registered with this registry.",
      s->getName().c_str());
  d_stats.insert(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::registerStat_() */

void StatisticsRegistry::unregisterStat(Stat* s)
{
#ifdef CVC4_STATISTICS_ON
  AlwaysAssert(s != nullptr);
  AlwaysAssert(d_stats.erase(s) > 0)
      << "Statistic `" << s->getName()
      << "' was not registered with this registry.";
#endif /* CVC4_STATISTICS_ON */
} /* StatisticsRegistry::unregisterStat() */

void StatisticsRegistry::flushStat(std::ostream &out) const {
#ifdef CVC4_STATISTICS_ON
  flushInformation(out);
#endif /* CVC4_STATISTICS_ON */
}

void StatisticsRegistry::flushInformation(std::ostream &out) const {
#ifdef CVC4_STATISTICS_ON
  this->StatisticsBase::flushInformation(out);
#endif /* CVC4_STATISTICS_ON */
}

void StatisticsRegistry::safeFlushInformation(int fd) const {
#ifdef CVC4_STATISTICS_ON
  this->StatisticsBase::safeFlushInformation(fd);
#endif /* CVC4_STATISTICS_ON */
}

RegisterStatistic::RegisterStatistic(StatisticsRegistry* reg, Stat* stat)
    : d_reg(reg),
      d_stat(stat) {
  CheckArgument(reg != NULL, reg,
                "You need to specify a statistics registry"
                "on which to set the statistic");
  d_reg->registerStat(d_stat);
}

RegisterStatistic::~RegisterStatistic() {
  d_reg->unregisterStat(d_stat);
}

}/* CVC4 namespace */
