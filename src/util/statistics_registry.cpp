/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Central statistics registry.
 *
 * The StatisticsRegistry that issues statistic proxy objects.
 */

#include "util/statistics_registry.h"

#include "options/base_options.h"
#include "util/statistics_public.h"

namespace cvc5 {

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
  if constexpr (Configuration::isStatisticsBuild())
  {
    d_lastSnapshot = std::make_unique<Snapshot>();
    for (const auto& s : d_stats)
    {
      if (!options::statisticsExpert() && s.second->d_expert) continue;
      if (!options::statisticsAll() && s.second->isDefault()) continue;
      d_lastSnapshot->emplace(
          s.first,
          s.second->getViewer());
    }
  }
}

StatisticBaseValue* StatisticsRegistry::get(const std::string& name) const
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    auto it = d_stats.find(name);
    if (it == d_stats.end()) return nullptr;
    return it->second.get();
  }
  return nullptr;
}

void StatisticsRegistry::print(std::ostream& os) const
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    for (const auto& s : d_stats)
    {
      if (!options::statisticsExpert() && s.second->d_expert) continue;
      if (!options::statisticsAll() && s.second->isDefault()) continue;
      os << s.first << " = " << *s.second << std::endl;
    }
  }
}

void StatisticsRegistry::printSafe(int fd) const
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    for (const auto& s : d_stats)
    {
      if (!options::statisticsExpert() && s.second->d_expert) continue;
      if (!options::statisticsAll() && s.second->isDefault()) continue;

      safe_print(fd, s.first);
      safe_print(fd, " = ");
      s.second->printSafe(fd);
      safe_print(fd, "\n");
    }
  }
}
void StatisticsRegistry::printDiff(std::ostream& os) const
{
  if constexpr (Configuration::isStatisticsBuild())
  {
    if (!d_lastSnapshot)
    {
      // we have no snapshot, print as usual
      print(os);
      return;
    }
    for (const auto& s : d_stats)
    {
      if (!options::statisticsExpert() && s.second->d_expert) continue;
      if (!options::statisticsAll() && s.second->isDefault())
      {
        auto oldit = d_lastSnapshot->find(s.first);
        if (oldit != d_lastSnapshot->end() && oldit->second != s.second->getViewer())
        {
          // present in the snapshot, now defaulted
          os << s.first << " = " << *s.second << " (was ";
          detail::print(os, oldit->second);
          os << ")" << std::endl;
        }
      }
      else
      {
        auto oldit = d_lastSnapshot->find(s.first);
        if (oldit == d_lastSnapshot->end())
        {
          // not present in the snapshot
          os << s.first << " = " << *s.second << " (was <default>)"
             << std::endl;
        }
        else if (oldit->second != s.second->getViewer())
        {
          // present in the snapshot, print old value
          os << s.first << " = " << *s.second << " (was ";
          detail::print(os, oldit->second);
          os << ")" << std::endl;
        }
      }
    }
  }
}

std::ostream& operator<<(std::ostream& os, const StatisticsRegistry& sr)
{
  sr.print(os);
  return os;
}

}  // namespace cvc5
