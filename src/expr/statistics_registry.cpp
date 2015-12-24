/*********************                                                        */
/*! \file statistics_registry.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/statistics_registry.h"

#include "base/cvc4_assert.h"
#include "expr/expr_manager.h"
#include "lib/clock_gettime.h"
#include "smt/smt_engine.h"

#ifndef __BUILDING_STATISTICS_FOR_EXPORT
#  include "smt/smt_engine_scope.h"
#endif /* ! __BUILDING_STATISTICS_FOR_EXPORT */

#ifdef CVC4_STATISTICS_ON
#  define __CVC4_USE_STATISTICS true
#else
#  define __CVC4_USE_STATISTICS false
#endif

#warning "TODO: Make StatisticsRegistry non-public again."
#warning "TODO: Make TimerStat non-public again."

namespace CVC4 {

/** Construct a statistics registry */
StatisticsRegistry::StatisticsRegistry(const std::string& name)
  throw(CVC4::IllegalArgumentException) :
  Stat(name) {

  d_prefix = name;
  if(__CVC4_USE_STATISTICS) {
    PrettyCheckArgument(d_name.find(s_regDelim) == std::string::npos, name,
                        "StatisticsRegistry names cannot contain the string \"%s\"",
                    s_regDelim.c_str());
  }
}

namespace stats {

// This is a friend of SmtEngine, just to reach in and get it.
// this isn't a class function because then there's a cyclic
// dependence.
inline StatisticsRegistry* getStatisticsRegistry(SmtEngine* smt) {
  return smt->d_statisticsRegistry;
}

inline StatisticsRegistry* getStatisticsRegistry(ExprManager* em) {
  return em->getStatisticsRegistry();
}

}/* CVC4::stats namespace */

#ifndef __BUILDING_STATISTICS_FOR_EXPORT

StatisticsRegistry* StatisticsRegistry::current() {
  return stats::getStatisticsRegistry(smt::currentSmtEngine());
}

void StatisticsRegistry::registerStat(Stat* s) throw(CVC4::IllegalArgumentException) {
#ifdef CVC4_STATISTICS_ON
  StatSet& stats = current()->d_stats;
  PrettyCheckArgument(stats.find(s) == stats.end(), s,
                      "Statistic `%s' was already registered with this registry.",
                      s->getName().c_str());
  stats.insert(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::registerStat() */

void StatisticsRegistry::unregisterStat(Stat* s) throw(CVC4::IllegalArgumentException) {
#ifdef CVC4_STATISTICS_ON
  StatSet& stats = current()->d_stats;
  PrettyCheckArgument(stats.find(s) != stats.end(), s,
                "Statistic `%s' was not registered with this registry.",
                s->getName().c_str());
  stats.erase(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::unregisterStat() */

#endif /* ! __BUILDING_STATISTICS_FOR_EXPORT */

void StatisticsRegistry::registerStat_(Stat* s) throw(CVC4::IllegalArgumentException) {
#ifdef CVC4_STATISTICS_ON
  PrettyCheckArgument(d_stats.find(s) == d_stats.end(), s);
  d_stats.insert(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::registerStat_() */

void StatisticsRegistry::unregisterStat_(Stat* s) throw(CVC4::IllegalArgumentException) {
#ifdef CVC4_STATISTICS_ON
  PrettyCheckArgument(d_stats.find(s) != d_stats.end(), s);
  d_stats.erase(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::unregisterStat_() */

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

void TimerStat::start() {
  if(__CVC4_USE_STATISTICS) {
    PrettyCheckArgument(!d_running, *this, "timer already running");
    clock_gettime(CLOCK_MONOTONIC, &d_start);
    d_running = true;
  }
}/* TimerStat::start() */

void TimerStat::stop() {
  if(__CVC4_USE_STATISTICS) {
    PrettyCheckArgument(d_running, *this, "timer not running");
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
  if(__CVC4_USE_STATISTICS && d_running) {
    ::timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    data += end - d_start;
  }
  return data;
}

SExpr TimerStat::getValue() const {
  ::timespec data = d_data;
  if(__CVC4_USE_STATISTICS && d_running) {
    ::timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    data += end - d_start;
  }
  std::stringstream ss;
  ss << std::fixed << std::setprecision(8) << data;
  return SExpr(Rational::fromDecimal(ss.str()));
}/* TimerStat::getValue() */

RegisterStatistic::RegisterStatistic(ExprManager& em, Stat* stat) :
  d_reg(stats::getStatisticsRegistry(&em)),
  d_stat(stat) {
  d_reg->registerStat_(d_stat);
}

RegisterStatistic::RegisterStatistic(SmtEngine& smt, Stat* stat) :
  d_reg(stats::getStatisticsRegistry(&smt)),
  d_stat(stat) {
  d_reg->registerStat_(d_stat);
}



}/* CVC4 namespace */

#undef __CVC4_USE_STATISTICS
