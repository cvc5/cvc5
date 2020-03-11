/*********************                                                        */
/*! \file statistics_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

/** Compute the sum of two timespecs. */
inline timespec& operator+=(timespec& a, const timespec& b) {
  using namespace CVC4;
  // assumes a.tv_nsec and b.tv_nsec are in range
  const long nsec_per_sec = 1000000000L; // one thousand million
  CheckArgument(a.tv_nsec >= 0 && a.tv_nsec < nsec_per_sec, a);
  CheckArgument(b.tv_nsec >= 0 && b.tv_nsec < nsec_per_sec, b);
  a.tv_sec += b.tv_sec;
  long nsec = a.tv_nsec + b.tv_nsec;
  Assert(nsec >= 0);
  if(nsec < 0) {
    nsec += nsec_per_sec;
    --a.tv_sec;
  }
  if(nsec >= nsec_per_sec) {
    nsec -= nsec_per_sec;
    ++a.tv_sec;
  }
  Assert(nsec >= 0 && nsec < nsec_per_sec);
  a.tv_nsec = nsec;
  return a;
}

/** Compute the difference of two timespecs. */
inline timespec& operator-=(timespec& a, const timespec& b) {
  using namespace CVC4;
  // assumes a.tv_nsec and b.tv_nsec are in range
  const long nsec_per_sec = 1000000000L; // one thousand million
  CheckArgument(a.tv_nsec >= 0 && a.tv_nsec < nsec_per_sec, a);
  CheckArgument(b.tv_nsec >= 0 && b.tv_nsec < nsec_per_sec, b);
  a.tv_sec -= b.tv_sec;
  long nsec = a.tv_nsec - b.tv_nsec;
  if(nsec < 0) {
    nsec += nsec_per_sec;
    --a.tv_sec;
  }
  if(nsec >= nsec_per_sec) {
    nsec -= nsec_per_sec;
    ++a.tv_sec;
  }
  Assert(nsec >= 0 && nsec < nsec_per_sec);
  a.tv_nsec = nsec;
  return a;
}

/** Add two timespecs. */
inline timespec operator+(const timespec& a, const timespec& b) {
  timespec result = a;
  return result += b;
}

/** Subtract two timespecs. */
inline timespec operator-(const timespec& a, const timespec& b) {
  timespec result = a;
  return result -= b;
}

/**
 * Compare two timespecs for equality.
 * This must be kept in sync with the copy in test/util/stats_black.h
 */
inline bool operator==(const timespec& a, const timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec == b.tv_sec && a.tv_nsec == b.tv_nsec;
}

/** Compare two timespecs for disequality. */
inline bool operator!=(const timespec& a, const timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a == b);
}

/** Compare two timespecs, returning true iff a < b. */
inline bool operator<(const timespec& a, const timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec < b.tv_sec ||
    (a.tv_sec == b.tv_sec && a.tv_nsec < b.tv_nsec);
}

/** Compare two timespecs, returning true iff a > b. */
inline bool operator>(const timespec& a, const timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return a.tv_sec > b.tv_sec ||
    (a.tv_sec == b.tv_sec && a.tv_nsec > b.tv_nsec);
}

/** Compare two timespecs, returning true iff a <= b. */
inline bool operator<=(const timespec& a, const timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a > b);
}

/** Compare two timespecs, returning true iff a >= b. */
inline bool operator>=(const timespec& a, const timespec& b) {
  // assumes a.tv_nsec and b.tv_nsec are in range
  return !(a < b);
}

/** Output a timespec on an output stream. */
std::ostream& operator<<(std::ostream& os, const timespec& t) {
  // assumes t.tv_nsec is in range
  StreamFormatScope format_scope(os);
  return os << t.tv_sec << "."
            << std::setfill('0') << std::setw(9) << std::right << t.tv_nsec;
}


/** Construct a statistics registry */
StatisticsRegistry::StatisticsRegistry(const std::string& name) : Stat(name)
{
  d_prefix = name;
  if(CVC4_USE_STATISTICS) {
    PrettyCheckArgument(d_name.find(s_regDelim) == std::string::npos, name,
                        "StatisticsRegistry names cannot contain the string \"%s\"",
                    s_regDelim.c_str());
  }
}

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

void TimerStat::start() {
  if(CVC4_USE_STATISTICS) {
    PrettyCheckArgument(!d_running, *this, "timer already running");
    clock_gettime(CLOCK_MONOTONIC, &d_start);
    d_running = true;
  }
}/* TimerStat::start() */

void TimerStat::stop() {
  if(CVC4_USE_STATISTICS) {
    AlwaysAssert(d_running) << "timer not running";
    ::timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    d_data += end - d_start;
    d_running = false;
  }
}/* TimerStat::stop() */

bool TimerStat::running() const {
  return d_running;
}/* TimerStat::running() */

timespec TimerStat::getData() const {
  ::timespec data = d_data;
  if(CVC4_USE_STATISTICS && d_running) {
    ::timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    data += end - d_start;
  }
  return data;
}

SExpr TimerStat::getValue() const {
  ::timespec data = d_data;
  if(CVC4_USE_STATISTICS && d_running) {
    ::timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    data += end - d_start;
  }
  std::stringstream ss;
  ss << std::fixed << std::setprecision(8) << data;
  return SExpr(Rational::fromDecimal(ss.str()));
}/* TimerStat::getValue() */


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

#undef CVC4_USE_STATISTICS
