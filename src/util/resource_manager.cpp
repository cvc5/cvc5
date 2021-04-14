/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This file provides the ResourceManager class. It can be used to impose
 * (cumulative and per-call) resource limits on the solver, as well as per-call
 * time limits.
 */
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

namespace cvc5 {

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

const char* toString(Resource r)
{
  switch (r)
  {
    case Resource::ArithPivotStep: return "ArithPivotStep";
    case Resource::ArithNlLemmaStep: return "ArithNlLemmaStep";
    case Resource::BitblastStep: return "BitblastStep";
    case Resource::BvEagerAssertStep: return "BvEagerAssertStep";
    case Resource::BvPropagationStep: return "BvPropagationStep";
    case Resource::BvSatConflictsStep: return "BvSatConflictsStep";
    case Resource::BvSatPropagateStep: return "BvSatPropagateStep";
    case Resource::BvSatSimplifyStep: return "BvSatSimplifyStep";
    case Resource::CnfStep: return "CnfStep";
    case Resource::DecisionStep: return "DecisionStep";
    case Resource::LemmaStep: return "LemmaStep";
    case Resource::NewSkolemStep: return "NewSkolemStep";
    case Resource::ParseStep: return "ParseStep";
    case Resource::PreprocessStep: return "PreprocessStep";
    case Resource::QuantifierStep: return "QuantifierStep";
    case Resource::RestartStep: return "RestartStep";
    case Resource::RewriteStep: return "RewriteStep";
    case Resource::SatConflictStep: return "SatConflictStep";
    case Resource::TheoryCheckStep: return "TheoryCheckStep";
    default: return "?Resource?";
  }
}

struct ResourceManager::Statistics
{
  ReferenceStat<std::uint64_t> d_resourceUnitsUsed;
  IntStat d_spendResourceCalls;
  std::vector<IntStat> d_resourceSteps;
  Statistics(StatisticsRegistry& stats);
  ~Statistics();

  void bump(Resource r, uint64_t amount)
  {
    bump_impl(static_cast<std::size_t>(r), amount, d_resourceSteps);
  }

 private:
  void bump_impl(std::size_t id, uint64_t amount, std::vector<IntStat>& stats)
  {
    Assert(stats.size() > id);
    stats[id] += amount;
  }

  StatisticsRegistry& d_statisticsRegistry;
};

ResourceManager::Statistics::Statistics(StatisticsRegistry& stats)
    : d_resourceUnitsUsed("resource::resourceUnitsUsed"),
      d_spendResourceCalls("resource::spendResourceCalls", 0),
      d_statisticsRegistry(stats)
{
  d_statisticsRegistry.registerStat(&d_resourceUnitsUsed);
  d_statisticsRegistry.registerStat(&d_spendResourceCalls);

  // Make sure we don't reallocate the vector
  d_resourceSteps.reserve(resman_detail::ResourceMax + 1);
  for (std::size_t id = 0; id <= resman_detail::ResourceMax; ++id)
  {
    Resource r = static_cast<Resource>(id);
    d_resourceSteps.emplace_back("resource::res::" + std::string(toString(r)),
                                 0);
    d_statisticsRegistry.registerStat(&d_resourceSteps[id]);
  }
}

ResourceManager::Statistics::~Statistics()
{
  d_statisticsRegistry.unregisterStat(&d_resourceUnitsUsed);
  d_statisticsRegistry.unregisterStat(&d_spendResourceCalls);

  for (auto& stat : d_resourceSteps)
  {
    d_statisticsRegistry.unregisterStat(&stat);
  }
}

bool parseOption(const std::string& optarg, std::string& name, uint64_t& weight)
{
  auto pos = optarg.find('=');
  // Check if there is a '='
  if (pos == std::string::npos) return false;
  // The name is the part before '='
  name = optarg.substr(0, pos);
  // The weight is the part after '='
  std::string num = optarg.substr(pos + 1);
  std::size_t converted;
  weight = std::stoull(num, &converted);
  // Check everything after '=' was converted
  return converted == num.size();
}

template <typename T, typename Weights>
bool setWeight(const std::string& name, uint64_t weight, Weights& weights)
{
  for (std::size_t i = 0; i < weights.size(); ++i)
  {
    if (name == toString(static_cast<T>(i)))
    {
      weights[i] = weight;
      return true;
    }
  }
  return false;
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
      d_statistics(new ResourceManager::Statistics(stats))
{
  d_statistics->d_resourceUnitsUsed.set(d_cumulativeResourceUsed);

  d_resourceWeights.fill(1);
  for (const auto& opt :
       options[cvc5::options::resourceWeightHolder__option_t()])
  {
    std::string name;
    uint64_t weight;
    if (parseOption(opt, name, weight))
    {
      if (setWeight<Resource>(name, weight, d_resourceWeights)) continue;
      throw OptionException("Did not recognize resource type " + name);
    }
  }
}

ResourceManager::~ResourceManager() {}

void ResourceManager::setResourceLimit(uint64_t units, bool cumulative)
{
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

void ResourceManager::spendResource(uint64_t amount)
{
  ++d_statistics->d_spendResourceCalls;
  d_cumulativeResourceUsed += amount;

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
  std::size_t i = static_cast<std::size_t>(r);
  Assert(d_resourceWeights.size() > i);
  d_statistics->bump(r, d_resourceWeights[i]);
  spendResource(d_resourceWeights[i]);
}

void ResourceManager::beginCall()
{
  d_perCallTimer.set(d_timeBudgetPerCall);
  d_thisCallResourceUsed = 0;

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

bool ResourceManager::limitOn() const
{
  return (d_resourceBudgetCumulative > 0) || (d_timeBudgetPerCall > 0)
         || (d_resourceBudgetPerCall > 0);
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

void ResourceManager::registerListener(Listener* listener)
{
  return d_listeners.push_back(listener);
}

}  // namespace cvc5
