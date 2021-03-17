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
 ** \brief Central statistics registry.
 **
 ** The StatisticsRegistry that issues statistic proxy objects.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATISTICS_REG_H
#define CVC4__UTIL__STATISTICS_REG_H

#include <iostream>
#include <map>
#include <memory>
#include <typeinfo>

#include "base/check.h"
#include "util/statistics_stats.h"
#include "util/statistics_value.h"

namespace CVC4 {

struct StatisticBaseValue;

/**
 * The central registry for statistics.
 * Internal stores statistic data objects and issues corresponding proxy
 * objects to modules that want to export statistics.
 * Provides registration methods (e.g. `registerAverage` or
 * `registerHistogram<T>`) that return the proxy object.
 *
 * Every statistic is identified by a name. If a statistic with the given
 * name is already registered, the registry issues a second proxy object
 * for that name. While this makes perfect sense for most statistic types,
 * it may lead to unexpected (though not undefined) behaviour for others.
 * For a reference statistic, for example, the internal data will simply
 * point to the object registered last.
 * Note that the type of the re-registered statistic must always match
 * the type of the previously registered statistic with the same name.
 */
class StatisticRegistry
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const StatisticRegistry& sr);
  /** Preregister public statistics */
  StatisticRegistry();

  /** Register a new running average statistic for `name` */
  AverageStats registerAverage(const std::string& name, bool expert = true)
  {
    return registerStat<AverageStats>(name, expert);
  }
  /** Register a new histogram statistic for `name` */
  template <typename T>
  HistogramStats<T> registerHistogram(const std::string& name,
                                      bool expert = true)
  {
    return registerStat<HistogramStats<T>>(name, expert);
  }
  /** Register a new integer statistic for `name` */
  IntStats registerInt(const std::string& name, bool expert = true)
  {
    return registerStat<IntStats>(name, expert);
  }
  /** Register a new reference statistic for `name` */
  template <typename T>
  ReferenceStats<T> registerReference(const std::string& name,
                                     const T& t,
                                     bool expert = true)
  {
    ReferenceStats<T> res = registerStat<ReferenceStats<T>>(name, expert);
    res.set(t);
    return res;
  }
  /** Register a new container size statistic for `name` */
  template <typename T>
  SizeStats<T> registerSize(const std::string& name,
                           const T& t,
                           bool expert = true)
  {
    SizeStats<T> res = registerStat<SizeStats<T>>(name, expert);
    res.set(t);
    return res;
  }
  /** Register a new timer statistic for `name` */
  TimerStats registerTimer(const std::string& name, bool expert = true)
  {
    return registerStat<TimerStats>(name, expert);
  }

  /** begin iteration */
  auto begin() const { return d_stats.begin(); }
  /** end iteration */
  auto end() const { return d_stats.end(); }

 private:
  /**
   * Helper method to register a new statistic.
   * If the name was already used, a new proxy object is created.
   * We check whether the type matches the type of the originally registered
   * statistic using `typeid`.
   */
  template <typename Stat>
  Stat registerStat(const std::string& name, bool expert)
  {
    auto it = d_stats.find(name);
    if (it == d_stats.end())
    {
      it = d_stats.emplace(name, std::make_unique<typename Stat::stat_type>())
               .first;
      it->second->d_expert = expert;
    }
    auto* ptr = it->second.get();
    Assert(typeid(*ptr) == typeid(typename Stat::stat_type))
        << "Statistic value " << name
        << " was registered again with a different type.";
    Assert(ptr->d_expert == expert)
        << "Statistic value " << name << " was previously registered as "
        << (ptr->d_expert ? "expert" : "public");
    return Stat(static_cast<typename Stat::stat_type*>(ptr));
  }

  std::map<std::string, std::unique_ptr<StatisticBaseValue>> d_stats;
};

std::ostream& operator<<(std::ostream& os, const StatisticRegistry& sr);

}  // namespace CVC4

#endif
