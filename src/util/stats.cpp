/*********************                                                        */
/*! \file stats.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "util/stats.h"
#include "expr/node_manager.h"
#include "expr/expr_manager_scope.h"
#include "lib/clock_gettime.h"

#ifdef CVC4_STATISTICS_ON
#  define __CVC4_USE_STATISTICS true
#else
#  define __CVC4_USE_STATISTICS false
#endif

using namespace CVC4;

std::string Stat::s_delim(",");
std::string StatisticsRegistry::s_regDelim("::");

StatisticsRegistry* StatisticsRegistry::current() {
  return NodeManager::currentNM()->getStatisticsRegistry();
}

void StatisticsRegistry::registerStat(Stat* s) throw(AssertionException) {
#ifdef CVC4_STATISTICS_ON
  StatSet& registeredStats = NodeManager::currentNM()->getStatisticsRegistry()->d_registeredStats;
  AlwaysAssert(registeredStats.find(s) == registeredStats.end(),
               "Statistic `%s' was already registered with this registry.", s->getName().c_str());
  registeredStats.insert(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::registerStat() */

void StatisticsRegistry::registerStat_(Stat* s) throw(AssertionException) {
#ifdef CVC4_STATISTICS_ON
  AlwaysAssert(d_registeredStats.find(s) == d_registeredStats.end());
  d_registeredStats.insert(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::registerStat_() */

void StatisticsRegistry::unregisterStat(Stat* s) throw(AssertionException) {
#ifdef CVC4_STATISTICS_ON
  StatSet& registeredStats = NodeManager::currentNM()->getStatisticsRegistry()->d_registeredStats;
  AlwaysAssert(registeredStats.find(s) != registeredStats.end(),
               "Statistic `%s' was not registered with this registry.", s->getName().c_str());
  registeredStats.erase(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::unregisterStat() */

void StatisticsRegistry::unregisterStat_(Stat* s) throw(AssertionException) {
#ifdef CVC4_STATISTICS_ON
  AlwaysAssert(d_registeredStats.find(s) != d_registeredStats.end());
  d_registeredStats.erase(s);
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::unregisterStat_() */

void StatisticsRegistry::flushInformation(std::ostream& out) const {
#ifdef CVC4_STATISTICS_ON
  for(StatSet::iterator i = d_registeredStats.begin();
      i != d_registeredStats.end();
      ++i) {
    Stat* s = *i;
    if(d_name != "") {
      out << d_name << s_regDelim;
    }
    s->flushStat(out);
    out << std::endl;
  }
#endif /* CVC4_STATISTICS_ON */
}/* StatisticsRegistry::flushInformation() */

void StatisticsRegistry::flushStat(std::ostream &out) const {;
#ifdef CVC4_STATISTICS_ON
  flushInformation(out);
#endif /* CVC4_STATISTICS_ON */
}

StatisticsRegistry::const_iterator StatisticsRegistry::begin() {
  return NodeManager::currentNM()->getStatisticsRegistry()->d_registeredStats.begin();
}/* StatisticsRegistry::begin() */

StatisticsRegistry::const_iterator StatisticsRegistry::end() {
  return NodeManager::currentNM()->getStatisticsRegistry()->d_registeredStats.end();
}/* StatisticsRegistry::end() */

void TimerStat::start() {
  if(__CVC4_USE_STATISTICS) {
    AlwaysAssert(!d_running);
    clock_gettime(CLOCK_MONOTONIC, &d_start);
    d_running = true;
  }
}/* TimerStat::start() */

void TimerStat::stop() {
  if(__CVC4_USE_STATISTICS) {
    AlwaysAssert(d_running);
    ::timespec end;
    clock_gettime(CLOCK_MONOTONIC, &end);
    d_data += end - d_start;
    d_running = false;
  }
}/* TimerStat::stop() */

RegisterStatistic::RegisterStatistic(ExprManager& em, Stat* stat) :
  d_reg(NULL),
  d_stat(stat) {
  ExprManagerScope ems(em);
  d_reg = StatisticsRegistry::current();
  d_reg->registerStat_(d_stat);
}
