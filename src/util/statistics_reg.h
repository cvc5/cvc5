/*********************                                                        */
/*! \file statistics_reg.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Basic statistics representation
 **
 ** The basic statistics classes.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_REG_H
#define CVC4__UTIL__STATISTICS_REG_H

#include <iostream>
#include <map>
#include <memory>

#include "util/statistics_stats.h"
#include "util/statistics_value.h"

namespace CVC4 {

struct StatisticBaseValue;

class StatisticRegistry
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const StatisticRegistry& sr);
  
  AverageStats registerAverage(const std::string& name)
  {
    return registerStat<AverageStats>(name);
  }
  template<typename T>
  HistogramStats<T> registerHistogram(const std::string& name)
  {
    return registerStat<HistogramStats<T>>(name);
  }
  IntStats registerInt(const std::string& name)
  {
    return registerStat<IntStats>(name);
  }
  template<typename T>
  ReferenceStat<T> registerReference(const std::string& name, const T& t)
  {
    ReferenceStat<T> res = registerStat<ReferenceStat<T>>(name);
    res.set(t);
    return res;
  }
  template<typename T>
  SizeStat<T> registerSize(const std::string& name, const T& t)
  {
    SizeStat<T> res = registerStat<SizeStat<T>>(name);
    res.set(t);
    return res;
  }
  TimerStats registerTimer(const std::string& name)
  {
    return registerStat<TimerStats>(name);
  }

  auto begin() const {
    return d_stats.begin();
  }
  auto end() const {
    return d_stats.end();
  }

 private:
  template <typename Stat>
  Stat registerStat(const std::string& name)
  {
    auto it = d_stats.find(name);
    if (it == d_stats.end())
    {
      it = d_stats.emplace(name, std::make_unique<typename Stat::stat_type>()).first;
    }
    return Stat(static_cast<typename Stat::stat_type*>(it->second.get()));
  }

  std::map<std::string, std::unique_ptr<StatisticBaseValue>> d_stats;
};

std::ostream& operator<<(std::ostream& os, const StatisticRegistry& sr)
{
  for (const auto& s : sr.d_stats)
  {
    os << s.first << " = " << *s.second << std::endl;
  }
  return os;
}

}  // namespace CVC4

#endif
