/*********************                                                        */
/*! \file statistics_registry.h
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

#ifndef CVC4__UTIL__STATISTICS_REGISTRY_H
#define CVC4__UTIL__STATISTICS_REGISTRY_H

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
class StatisticsRegistry
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const StatisticsRegistry& sr);
  /** Preregister public statistics */
  StatisticsRegistry(bool register_public = true);

  /** Register a new running average statistic for `name` */
  AverageStat registerAverage(const std::string& name, bool expert = true);
  /** Register a new histogram statistic for `name` */
  template <typename T>
  HistogramStat<T> registerHistogram(const std::string& name,
                                     bool expert = true)
  {
    return registerStat<HistogramStat<T>>(name, expert);
  }
  /** Register a new integer statistic for `name` */
  IntStats registerInt(const std::string& name, bool expert = true);
  /** Register a new reference statistic for `name` */
  template <typename T>
  ReferenceStat<T> registerReference(const std::string& name,
                                     bool expert = true)
  {
    return registerStat<ReferenceStat<T>>(name, expert);
  }
  /** Register a new reference statistic for `name` */
  template <typename T>
  ReferenceStat<T> registerReference(const std::string& name,
                                     const T& t,
                                     bool expert = true)
  {
    ReferenceStat<T> res = registerStat<ReferenceStat<T>>(name, expert);
    res.set(t);
    return res;
  }
  /** Register a new container size statistic for `name` */
  template <typename T>
  SizeStat<T> registerSize(const std::string& name,
                           const T& t,
                           bool expert = true)
  {
    SizeStat<T> res = registerStat<SizeStat<T>>(name, expert);
    res.set(t);
    return res;
  }
  /** Register a new timer statistic for `name` */
  TimerStat registerTimer(const std::string& name, bool expert = true);
  /** Register a new value statistic for `name` */
  template <typename T>
  ValueStat<T> registerValue(const std::string& name,
                             const T& init,
                             bool expert = true)
  {
    ValueStat<T> res = registerStat<ValueStat<T>>(name, expert);
    res.set(init);
    return res;
  }

  /** begin iteration */
  auto begin() const { return d_stats.begin(); }
  /** end iteration */
  auto end() const { return d_stats.end(); }

  StatisticBaseValue* get(const std::string& name) const;

  void print(std::ostream& os, bool expert = false) const;
  void print_safe(int fd, bool expert = false) const;

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
    if (CVC4_USE_STATISTICS)
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
      it->second->d_expert = it->second->d_expert || expert;
      return Stat(static_cast<typename Stat::stat_type*>(ptr));
    }
    return Stat(nullptr);
  }

  std::map<std::string, std::unique_ptr<StatisticBaseValue>> d_stats;
};

std::ostream& operator<<(std::ostream& os, const StatisticsRegistry& sr);

}  // namespace CVC4

#endif
