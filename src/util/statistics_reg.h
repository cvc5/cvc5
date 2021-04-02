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

namespace cvc5 {

struct StatisticBaseValue;

/**
 * The central registry for statistics.
 * Internally stores statistic data objects and issues corresponding proxy
 * objects to modules that want to expose statistics.
 * Provides registration methods (e.g. `registerAverage` or
 * `registerHistogram<T>`) that return the proxy object.
 * The different statistics are explained in more detail in statistics_stats.h
 *
 * Every statistic is identified by a name. If a statistic with the given
 * name is already registered, the registry issues another proxy object
 * for that name using the same data it already holds for this name.
 * While this makes perfect sense for most statistic types, it may lead to
 * unexpected (though not undefined) behaviour for others. For a reference
 * statistic, for example, the internal data will simply point to the object
 * registered last.
 * Note that the type of the re-registered statistic must always match
 * the type of the previously registered statistic with the same name.
 *
 * We generally distinguish between public (non-expert) and private (expert)
 * statistics. By default, `--stats` only shows public statistics. Private
 * ones are printed as well if `--all-statistics` is set.
 * All registration methods have a trailing argument `expert`, defaulting to
 * true.
 *
 * If statistics are disabled entirely (i.e. the cmake option
 * `ENABLE_STATISTICS` is not set), the registry still issues proxy objects
 * that can be used normally.
 * However, no data is stored in the registry and the modification functions
 * of the proxy objects do nothing.
 */
class StatisticsRegistry
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const StatisticsRegistry& sr);

  using Snapshot = std::map<std::string, StatExportData>;

  /**
   * If `registerPublic` is true, all statistics that are public are
   * pre-registered as such. This argument mostly exists so that unit tests
   * can disable this pre-registration.
   */
  StatisticsRegistry(bool registerPublic = true);

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
  IntStat registerInt(const std::string& name, bool expert = true);

  /** Register a new reference statistic for `name` */
  template <typename T>
  ReferenceStat<T> registerReference(const std::string& name,
                                     bool expert = true)
  {
    return registerStat<ReferenceStat<T>>(name, expert);
  }
  /**
   * Register a new reference statistic for `name` and initialize it to
   * refer to `t`.
   */
  template <typename T>
  ReferenceStat<T> registerReference(const std::string& name,
                                     const T& t,
                                     bool expert = true)
  {
    ReferenceStat<T> res = registerStat<ReferenceStat<T>>(name, expert);
    res.set(t);
    return res;
  }

  /**
   * Register a new container size statistic for `name` and initialize it
   * to refer to `t`.
   */
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

  /** Register a new value statistic for `name`. */
  template <typename T>
  ValueStat<T> registerValue(const std::string& name, bool expert = true)
  {
    return registerStat<ValueStat<T>>(name, expert);
  }

  /** Register a new value statistic for `name` and set it to `init`. */
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

  /**
   * Store the current state of the statistics to allow for printing a diff
   * using `printDiff`.
   */
  void storeSnapshot();

  /**
   * Obtain a single statistic by name. Returns nullptr if no statistic has
   * been registered for this name.
   */
  StatisticBaseValue* get(const std::string& name) const;

  /**
   * Print all statistics to the given output stream.
   */
  void print(std::ostream& os) const;
  /**
   * Print all statistics in a safe manner to the given file descriptor.
   */
  void printSafe(int fd) const;
  /**
   * Print all statistics as a diff to the last snapshot that was stored by
   * calling `storeSnapshot`.
   */
  void printDiff(std::ostream& os) const;

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
    if constexpr (Configuration::isStatisticsBuild())
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
      it->second->d_expert = it->second->d_expert && expert;
      return Stat(static_cast<typename Stat::stat_type*>(ptr));
    }
    return Stat(nullptr);
  }

  /**
   * Holds (and owns) all statistic values, indexed by the name they were
   * registered for.
   */
  std::map<std::string, std::unique_ptr<StatisticBaseValue>> d_stats;

  /**
   * Holds a snapshot of the statistic values as StatExportData.
   * The current state can be saved to this snapshot using `storeSnapshot`,
   * which is then used in the next call to `printDiff`, but the data is not
   * exposed otherwise.
   * As this snapshot is only used by `printDiff`, which honors the relevant
   * options `--stats-expert` and `--stats-unset`, the snapshot is populated
   * by `storeSnapshot` to contain only those values that would be printed.
   */
  std::unique_ptr<Snapshot> d_lastSnapshot;
};

/** Calls `sr.print(os)`. */
std::ostream& operator<<(std::ostream& os, const StatisticsRegistry& sr);

}  // namespace cvc5

#endif
