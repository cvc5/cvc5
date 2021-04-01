/*********************                                                        */
/*! \file resource_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer, Mathias Preiner, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/
#include "util/resource_manager.h"

#include <algorithm>
#include <ostream>

#include "base/check.h"
#include "base/listener.h"
#include "base/output.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "util/statistics_registry.h"

using namespace std;

namespace CVC5 {

bool WallClockTimer::on() const
{
  // default-constructed time points are at the respective epoch
  return d_limit.time_since_epoch().count() != 0;
}
void WallClockTimer::set(uint64_t millis)
{
  if (millis == 0)
  {
    // reset / deactivate
    d_start = time_point();
    d_limit = time_point();
  }
  else
  {
    // set to now() + millis
    d_start = clock::now();
    d_limit = d_start + std::chrono::milliseconds(millis);
  }
}
uint64_t WallClockTimer::elapsed() const
{
  if (!on()) return 0;
  // now() - d_start casted to milliseconds
  return std::chrono::duration_cast<std::chrono::milliseconds>(clock::now()
                                                               - d_start)
      .count();
}
bool WallClockTimer::expired() const
{
  // whether d_limit is in the past
  if (!on()) return false;
  return d_limit <= clock::now();
}

/*---------------------------------------------------------------------------*/

struct ResourceManager::Statistics
{
  ReferenceStat<uint64_t> d_resourceUnitsUsed;
  IntStat d_spendResourceCalls;
  IntStat d_numArithPivotStep;
  IntStat d_numArithNlLemmaStep;
  IntStat d_numBitblastStep;
  IntStat d_numBvEagerAssertStep;
  IntStat d_numBvPropagationStep;
  IntStat d_numBvSatConflictsStep;
  IntStat d_numBvSatPropagateStep;
  IntStat d_numBvSatSimplifyStep;
  IntStat d_numCnfStep;
  IntStat d_numDecisionStep;
  IntStat d_numLemmaStep;
  IntStat d_numNewSkolemStep;
  IntStat d_numParseStep;
  IntStat d_numPreprocessStep;
  IntStat d_numQuantifierStep;
  IntStat d_numRestartStep;
  IntStat d_numRewriteStep;
  IntStat d_numSatConflictStep;
  IntStat d_numTheoryCheckStep;
  Statistics(StatisticsRegistry& stats);
};

ResourceManager::Statistics::Statistics(StatisticsRegistry& stats)
    : d_resourceUnitsUsed(stats.registerReference<uint64_t>("resource::resourceUnitsUsed")),
      d_spendResourceCalls(stats.registerInt("resource::spendResourceCalls")),
      d_numArithPivotStep(stats.registerInt("resource::ArithPivotStep")),
      d_numArithNlLemmaStep(stats.registerInt("resource::ArithNlLemmaStep")),
      d_numBitblastStep(stats.registerInt("resource::BitblastStep")),
      d_numBvEagerAssertStep(stats.registerInt("resource::BvEagerAssertStep")),
      d_numBvPropagationStep(stats.registerInt("resource::BvPropagationStep")),
      d_numBvSatConflictsStep(stats.registerInt("resource::BvSatConflictsStep")),
      d_numBvSatPropagateStep(stats.registerInt("resource::BvSatPropagateStep")),
      d_numBvSatSimplifyStep(stats.registerInt("resource::BvSatSimplifyStep")),
      d_numCnfStep(stats.registerInt("resource::CnfStep")),
      d_numDecisionStep(stats.registerInt("resource::DecisionStep")),
      d_numLemmaStep(stats.registerInt("resource::LemmaStep")),
      d_numNewSkolemStep(stats.registerInt("resource::NewSkolemStep")),
      d_numParseStep(stats.registerInt("resource::ParseStep")),
      d_numPreprocessStep(stats.registerInt("resource::PreprocessStep")),
      d_numQuantifierStep(stats.registerInt("resource::QuantifierStep")),
      d_numRestartStep(stats.registerInt("resource::RestartStep")),
      d_numRewriteStep(stats.registerInt("resource::RewriteStep")),
      d_numSatConflictStep(stats.registerInt("resource::SatConflictStep")),
      d_numTheoryCheckStep(stats.registerInt("resource::TheoryCheckStep"))
{
}

/*---------------------------------------------------------------------------*/

ResourceManager::ResourceManager(StatisticsRegistry& stats, Options& options)
    : d_perCallTimer(),
      d_timeBudgetPerCall(0),
      d_resourceBudgetCumulative(0),
      d_resourceBudgetPerCall(0),
      d_cumulativeTimeUsed(0),
      d_cumulativeResourceUsed(0),
      d_thisCallResourceUsed(0),
      d_thisCallResourceBudget(0),
      d_on(false),
      d_statistics(new ResourceManager::Statistics(stats)),
      d_options(options)

{
  d_statistics->d_resourceUnitsUsed.set(d_cumulativeResourceUsed);
}

ResourceManager::~ResourceManager() {}

void ResourceManager::setResourceLimit(uint64_t units, bool cumulative)
{
  d_on = true;
  if (cumulative)
  {
    Trace("limit") << "ResourceManager: setting cumulative resource limit to "
                   << units << endl;
    d_resourceBudgetCumulative =
        (units == 0) ? 0 : (d_cumulativeResourceUsed + units);
    d_thisCallResourceBudget = d_resourceBudgetCumulative;
  }
  else
  {
    Trace("limit") << "ResourceManager: setting per-call resource limit to "
                   << units << endl;
    d_resourceBudgetPerCall = units;
  }
}

void ResourceManager::setTimeLimit(uint64_t millis)
{
  d_on = true;
  Trace("limit") << "ResourceManager: setting per-call time limit to " << millis
                 << " ms" << endl;
  d_timeBudgetPerCall = millis;
  // perCall timer will be set in beginCall
}

uint64_t ResourceManager::getResourceUsage() const
{
  return d_cumulativeResourceUsed;
}

uint64_t ResourceManager::getTimeUsage() const { return d_cumulativeTimeUsed; }

uint64_t ResourceManager::getResourceRemaining() const
{
  if (d_resourceBudgetCumulative <= d_cumulativeResourceUsed) return 0;
  return d_resourceBudgetCumulative - d_cumulativeResourceUsed;
}

void ResourceManager::spendResource(unsigned amount)
{
  ++d_statistics->d_spendResourceCalls;
  d_cumulativeResourceUsed += amount;
  if (!d_on) return;

  Debug("limit") << "ResourceManager::spendResource()" << std::endl;
  d_thisCallResourceUsed += amount;
  if (out())
  {
    Trace("limit") << "ResourceManager::spendResource: interrupt!" << std::endl;
    Trace("limit") << "          on call "
                   << d_statistics->d_spendResourceCalls.get() << std::endl;
    if (outOfTime())
    {
      Trace("limit") << "ResourceManager::spendResource: elapsed time"
                     << d_perCallTimer.elapsed() << std::endl;
    }

    for (Listener* l : d_listeners)
    {
      l->notify();
    }
  }
}

void ResourceManager::spendResource(Resource r)
{
  uint32_t amount = 0;
  switch (r)
  {
    case Resource::ArithPivotStep:
      amount = d_options[options::arithPivotStep];
      ++d_statistics->d_numArithPivotStep;
      break;
    case Resource::ArithNlLemmaStep:
      amount = d_options[options::arithNlLemmaStep];
      ++d_statistics->d_numArithNlLemmaStep;
      break;
    case Resource::BitblastStep:
      amount = d_options[options::bitblastStep];
      ++d_statistics->d_numBitblastStep;
      break;
    case Resource::BvEagerAssertStep:
      amount = d_options[options::bvEagerAssertStep];
      ++d_statistics->d_numBvEagerAssertStep;
      break;
    case Resource::BvPropagationStep:
      amount = d_options[options::bvPropagationStep];
      ++d_statistics->d_numBvPropagationStep;
      break;
    case Resource::BvSatConflictsStep:
      amount = d_options[options::bvSatConflictStep];
      ++d_statistics->d_numBvSatConflictsStep;
      break;
    case Resource::BvSatPropagateStep:
      amount = d_options[options::bvSatPropagateStep];
      ++d_statistics->d_numBvSatPropagateStep;
      break;
    case Resource::BvSatSimplifyStep:
      amount = d_options[options::bvSatSimplifyStep];
      ++d_statistics->d_numBvSatSimplifyStep;
      break;
    case Resource::CnfStep:
      amount = d_options[options::cnfStep];
      ++d_statistics->d_numCnfStep;
      break;
    case Resource::DecisionStep:
      amount = d_options[options::decisionStep];
      ++d_statistics->d_numDecisionStep;
      break;
    case Resource::LemmaStep:
      amount = d_options[options::lemmaStep];
      ++d_statistics->d_numLemmaStep;
      break;
    case Resource::NewSkolemStep:
      amount = d_options[options::newSkolemStep];
      ++d_statistics->d_numNewSkolemStep;
      break;
    case Resource::ParseStep:
      amount = d_options[options::parseStep];
      ++d_statistics->d_numParseStep;
      break;
    case Resource::PreprocessStep:
      amount = d_options[options::preprocessStep];
      ++d_statistics->d_numPreprocessStep;
      break;
    case Resource::QuantifierStep:
      amount = d_options[options::quantifierStep];
      ++d_statistics->d_numQuantifierStep;
      break;
    case Resource::RestartStep:
      amount = d_options[options::restartStep];
      ++d_statistics->d_numRestartStep;
      break;
    case Resource::RewriteStep:
      amount = d_options[options::rewriteStep];
      ++d_statistics->d_numRewriteStep;
      break;
    case Resource::SatConflictStep:
      amount = d_options[options::satConflictStep];
      ++d_statistics->d_numSatConflictStep;
      break;
    case Resource::TheoryCheckStep:
      amount = d_options[options::theoryCheckStep];
      ++d_statistics->d_numTheoryCheckStep;
      break;
    default: Unreachable() << "Invalid resource " << std::endl;
  }
  spendResource(amount);
}

void ResourceManager::beginCall()
{
  d_perCallTimer.set(d_timeBudgetPerCall);
  d_thisCallResourceUsed = 0;
  if (!d_on) return;

  if (d_resourceBudgetCumulative > 0)
  {
    // Compute remaining cumulative resource budget
    d_thisCallResourceBudget =
        d_resourceBudgetCumulative - d_cumulativeResourceUsed;
  }
  if (d_resourceBudgetPerCall > 0)
  {
    // Check if per-call resource budget is even smaller
    if (d_resourceBudgetPerCall < d_thisCallResourceBudget)
    {
      d_thisCallResourceBudget = d_resourceBudgetPerCall;
    }
  }
}

void ResourceManager::endCall()
{
  d_cumulativeTimeUsed += d_perCallTimer.elapsed();
  d_perCallTimer.set(0);
  d_thisCallResourceUsed = 0;
}

bool ResourceManager::cumulativeLimitOn() const
{
  return d_resourceBudgetCumulative > 0;
}

bool ResourceManager::perCallLimitOn() const
{
  return (d_timeBudgetPerCall > 0) || (d_resourceBudgetPerCall > 0);
}

bool ResourceManager::outOfResources() const
{
  if (d_resourceBudgetPerCall > 0)
  {
    // Check if per-call resources are exhausted
    if (d_thisCallResourceUsed >= d_resourceBudgetPerCall)
    {
      return true;
    }
  }
  if (d_resourceBudgetCumulative > 0)
  {
    // Check if cumulative resources are exhausted
    if (d_cumulativeResourceUsed >= d_resourceBudgetCumulative)
    {
      return true;
    }
  }
  return false;
}

bool ResourceManager::outOfTime() const
{
  if (d_timeBudgetPerCall == 0) return false;
  return d_perCallTimer.expired();
}

void ResourceManager::enable(bool on)
{
  Trace("limit") << "ResourceManager::enable(" << on << ")\n";
  d_on = on;
}

void ResourceManager::registerListener(Listener* listener)
{
  return d_listeners.push_back(listener);
}

} // namespace CVC5
