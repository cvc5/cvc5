/*********************                                                        */
/*! \file statistics_registry.cpp
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

#include "util/statistics_registry.h"

#include "util/statistics_public.h"

namespace CVC4 {

StatisticsRegistry::StatisticsRegistry(bool registerPublic)
{
  if (registerPublic)
  {
    registerPublicStatistics(*this);
  }
}

AverageStat StatisticsRegistry::registerAverage(const std::string& name,
                                                bool expert)
{
  return registerStat<AverageStat>(name, expert);
}
IntStat StatisticsRegistry::registerInt(const std::string& name, bool expert)
{
  return registerStat<IntStat>(name, expert);
}
TimerStat StatisticsRegistry::registerTimer(const std::string& name,
                                            bool expert)
{
  return registerStat<TimerStat>(name, expert);
}

void StatisticsRegistry::storeSnapshot()
{
  if constexpr (CVC4_USE_STATISTICS)
  {
    d_lastSnapshot = std::make_unique<Snapshot>();
    for (const auto& s : d_stats)
    {
      if (!options::statisticsExpert() && s.second->d_expert) continue;
      if (!options::statisticsUnset() && !s.second->hasValue()) continue;
      d_lastSnapshot->emplace(
          s.first,
          s.second->hasValue() ? s.second->getViewer() : StatExportData{});
    }
  }
}

StatisticBaseValue* StatisticsRegistry::get(const std::string& name) const
{
  if constexpr (CVC4_USE_STATISTICS)
  {
    auto it = d_stats.find(name);
    if (it == d_stats.end()) return nullptr;
    return it->second.get();
  }
  return nullptr;
}

void StatisticsRegistry::print(std::ostream& os, bool expert) const
{
  for (const auto& s : d_stats)
  {
    if (expert || (!s.second->d_expert && s.second->hasValue()))
    {
      os << s.first << " = ";
      s.second->print(os);
      os << std::endl;
    }
  }
}
void StatisticsRegistry::print_safe(int fd, bool expert) const
{
  for (const auto& s : d_stats)
  {
    if (expert || (!s.second->d_expert && s.second->hasValue()))
    {
      safe_print(fd, s.first);
      safe_print(fd, " = ");
      s.second->print_safe(fd);
      safe_print(fd, '\n');
    }
  }
}
void StatisticsRegistry::printDiff(std::ostream& os) const {
  if constexpr (CVC4_USE_STATISTICS) {
    if (!d_lastSnapshot) {
      print(os);
      return;
    }
    for (const auto& s : d_stats)
    {
      if (!options::statisticsExpert() && s.second->d_expert) continue;
      if (!options::statisticsUnset() && !s.second->hasValue()) continue;
      auto oldit = d_lastSnapshot->find(s.first);
      if (oldit == d_lastSnapshot->end()) {
        os << s.first << " = " << *s.second << " (was <unset>)" << std::endl;
      } else if (oldit->second != s.second->getViewer()) {
        os << s.first << " = " << *s.second << " (was ";
        detail::print(os, oldit->second);
        os << ")" << std::endl;
      }
    }
  }
}

std::ostream& operator<<(std::ostream& os, const StatisticsRegistry& sr)
{
  sr.print(os);
  return os;
}

}  // namespace CVC4
