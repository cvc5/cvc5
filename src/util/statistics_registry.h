/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics utility classes
 *
 * Statistics utility classes, including classes for holding (and referring
 * to) statistics, the statistics registry, and some other associated
 * classes.
 *
 * This file is somewhat unique in that it is a "cvc4_private_library.h"
 * header. Because of this, most classes need to be marked as CVC4_EXPORT.
 * This is because CVC4_EXPORT is connected to the visibility of the linkage
 * in the object files for the class. It does not dictate what headers are
 * installed.
 * Because the StatisticsRegistry and associated classes are built into
 * libutil, which is used by libcvc4, and then later used by the libmain
 * without referring to libutil as well. Thus the without marking these as
 * CVC4_EXPORT the symbols would be external in libutil, internal in libcvc4,
 * and not be visible to libmain and linking would fail.
 * You can debug this using "nm" on the .so and .o files in the builds/
 * directory. See
 * http://eli.thegreenplace.net/2013/07/09/library-order-in-static-linking
 * for a longer discussion on symbol visibility.
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
 * HistogramStat counts instances of some type T. It is implemented as a
 * std::map<T, std::uint64_t>.
 *
 * IntegralHistogramStat is a (conceptual) specialization of HistogramStat
 * for types that are (convertible to) integral. This allows to use a
 * std::vector<std::uint64_t> instead of a std::map.
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

#include "cvc4_private_library.h"

#ifndef CVC5__STATISTICS_REGISTRY_H
#define CVC5__STATISTICS_REGISTRY_H

#include <ctime>
#include <iomanip>
#include <map>
#include <sstream>
#include <vector>

#ifdef CVC5_STATISTICS_ON
#define CVC5_USE_STATISTICS true
#else
#define CVC5_USE_STATISTICS false
#endif

#include "base/exception.h"
#include "cvc4_export.h"
#include "util/safe_print.h"
#include "util/statistics.h"
#include "util/stats_base.h"

namespace cvc5 {

/** A statistic that contains a SExpr. */
class SExprStat : public Stat {
private:
  SExpr d_data;

public:

  /**
   * Construct a SExpr-valued statistic with the given name and
   * initial value.
   */
  SExprStat(const std::string& name, const SExpr& init) :
    Stat(name), d_data(init){}

  void flushInformation(std::ostream& out) const override
  {
    out << d_data;
  }

  void safeFlushInformation(int fd) const override
  {
    // SExprStat is only used in statistics.cpp in copyFrom, which we cannot
    // do in a signal handler anyway.
    safe_print(fd, "<unsupported>");
  }

  SExpr getValue() const override { return d_data; }

};/* class SExprStat */

/****************************************************************************/
/* Statistics Registry                                                      */
/****************************************************************************/

/**
 * The main statistics registry.  This registry maintains the list of
 * currently active statistics and is able to "flush" them all.
 */
class CVC4_EXPORT StatisticsRegistry : public StatisticsBase
{
 private:
  /** Private copy constructor undefined (no copy permitted). */
  StatisticsRegistry(const StatisticsRegistry&) = delete;

public:

  /** Construct an nameless statistics registry */
  StatisticsRegistry() {}

  void flushStat(std::ostream& out) const;

  void flushInformation(std::ostream& out) const;

  void safeFlushInformation(int fd) const;

  SExpr getValue() const
  {
    std::vector<SExpr> v;
    for(StatSet::iterator i = d_stats.begin(); i != d_stats.end(); ++i) {
      std::vector<SExpr> w;
      w.push_back(SExpr((*i)->getName()));
      w.push_back((*i)->getValue());
      v.push_back(SExpr(w));
    }
    return SExpr(v);
  }

  /** Register a new statistic */
  void registerStat(Stat* s);

  /** Unregister a new statistic */
  void unregisterStat(Stat* s);

}; /* class StatisticsRegistry */

/**
 * Resource-acquisition-is-initialization idiom for statistics
 * registry.  Useful for stack-based statistics (like in the driver).
 * This RAII class only does registration and unregistration.
 */
class CVC4_EXPORT RegisterStatistic
{
 public:
  RegisterStatistic(StatisticsRegistry* reg, Stat* stat);
  ~RegisterStatistic();

private:
  StatisticsRegistry* d_reg;
  Stat* d_stat;

}; /* class RegisterStatistic */

}  // namespace cvc5

#endif /* CVC5__STATISTICS_REGISTRY_H */
