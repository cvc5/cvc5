/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Central statistics registry.
 *
 * The StatisticsRegistry that issues statistic proxy objects.
 */

/**
 * On the design of the statistics:
 *
 * Stat is the abstract base class for all statistic values.
 * It stores the name and provides (fully virtual) methods
 * flushInformation() and safeFlushInformation().
 *
 * BackedStat is an abstract templated base class for statistic values
 * that store the data themselves. It takes care of printing them already
 * and derived classes usually only need to provide methods to set the
 * value.
 *
 * ReferenceStat holds a reference (conceptually, it is implemented as a
 * const pointer) to some data that is stored outside of the statistic.
 *
 * IntStat is a BackedStat<std::int64_t>.
 *
 * SizeStat holds a const reference to some container and provides the
 * size of this container.
 *
 * AverageStat is a BackedStat<double>.
 *
 * HistogramStat counts instances of some type T. We assume that T is either an
 * integral type, or an enum type (that is convertible to an interval type).
 * This allows a more efficient implementation as std::vector<std::uint64_t>
 * instead of a std::map<T, uint64_t>.
 *
 * TimerStat uses std::chrono to collect timing information. It is
 * implemented as BackedStat<std::chrono::duration> and provides methods
 * start() and stop(), accumulating times it was activated. It provides
 * the convenience class CodeTimer to allow for RAII-style usage.
 *
 *
 * All statistic classes should protect their custom methods using
 *   if (CVC5_USE_STATISTICS) { ... }
 * Output methods (flushInformation() and safeFlushInformation()) are only
 * called when statistics are enabled and need no protection.
 *
 *
 * The statistic classes try to implement a consistent interface:
 * - if we store some generic data, we implement set()
 * - if we (conceptually) store a set of values, we implement operator<<()
 * - if there are standard operations for the stored data, we implement these
 *   (like operator++() or operator+=())
 */

#include "cvc5_private_library.h"

#ifndef CVC5__STATISTICS_REGISTRY_H
#define CVC5__STATISTICS_REGISTRY_H

#include <iostream>
#include <map>
#include <memory>
#include <typeinfo>

#include "base/check.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"
#include "util/statistics_value.h"

namespace cvc5::internal {

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
 * We generally distinguish between public and internal statistics.
 * By default, `--stats` only shows public statistics. Internal
 * ones are printed as well if `--stats-internal` is set.
 * All registration methods have a trailing argument `internal`, defaulting to
 * true.
 *
 * If statistics are disabled entirely (i.e. the cmake option
 * `ENABLE_STATISTICS` is not set), the registry still issues proxy objects
 * that can be used normally.
 * However, no data is stored in the registry and the modification functions
 * of the proxy objects do nothing.
 */
class StatisticsRegistry : protected EnvObj
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
  StatisticsRegistry(Env& env, bool registerPublic = true);

  /** Register a new running average statistic for `name` */

  AverageStat registerAverage(const std::string& name, bool internal = true);
  /** Register a new histogram statistic for `name` */
  template <typename T>
  HistogramStat<T> registerHistogram(const std::string& name,
                                     bool internal = true)
  {
    return registerStat<HistogramStat<T>>(name, internal);
  }

  /** Register a new integer statistic for `name` */
  IntStat registerInt(const std::string& name, bool internal = true);

  /** Register a new reference statistic for `name` */
  template <typename T>
  ReferenceStat<T> registerReference(const std::string& name,
                                     bool internal = true)
  {
    return registerStat<ReferenceStat<T>>(name, internal);
  }
  /**
   * Register a new reference statistic for `name` and initialize it to
   * refer to `t`.
   */
  template <typename T>
  ReferenceStat<T> registerReference(const std::string& name,
                                     const T& t,
                                     bool internal = true)
  {
    ReferenceStat<T> res = registerStat<ReferenceStat<T>>(name, internal);
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
                           bool internal = true)
  {
    SizeStat<T> res = registerStat<SizeStat<T>>(name, internal);
    res.set(t);
    return res;
  }

  /** Register a new timer statistic for `name` */
  TimerStat registerTimer(const std::string& name, bool internal = true);

  /** Register a new value statistic for `name`. */
  template <typename T>
  ValueStat<T> registerValue(const std::string& name, bool internal = true)
  {
    return registerStat<ValueStat<T>>(name, internal);
  }

  /** Register a new value statistic for `name` and set it to `init`. */
  template <typename T>
  ValueStat<T> registerValue(const std::string& name,
                             const T& init,
                             bool internal = true)
  {
    ValueStat<T> res = registerStat<ValueStat<T>>(name, internal);
    res.set(init);
    return res;
  }

  /** begin iteration */
  auto begin() const { return d_stats.begin(); }
  /** end iteration */
  auto end() const { return d_stats.end(); }

  /**
   * Obtain the current state of all statistics.
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
   * Print all statistics as a diff to the last stored snapshot.
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
  Stat registerStat(const std::string& name, bool internal)
  {
    if constexpr (configuration::isStatisticsBuild())
    {
      auto it = d_stats.find(name);
      if (it == d_stats.end())
      {
        it = d_stats.emplace(name, std::make_unique<typename Stat::stat_type>())
                 .first;
        it->second->d_internal = internal;
      }
      auto* ptr = it->second.get();
      Assert(typeid(*ptr) == typeid(typename Stat::stat_type))
          << "Statistic value " << name
          << " was registered again with a different type.";
      it->second->d_internal = it->second->d_internal && internal;
      return Stat(static_cast<typename Stat::stat_type*>(ptr));
    }
    return Stat(nullptr);
  }

  /**
   * Holds (and owns) all statistic values, indexed by the name they were
   * registered for.
   */
  std::map<std::string, std::unique_ptr<StatisticBaseValue>> d_stats;

  std::unique_ptr<Snapshot> d_lastSnapshot;
};

/** Calls `sr.print(os)`. */
std::ostream& operator<<(std::ostream& os, const StatisticsRegistry& sr);

}  // namespace cvc5::internal

#endif /* CVC5__STATISTICS_REGISTRY_H */
