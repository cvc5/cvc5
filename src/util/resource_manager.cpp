/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Liana Hadarean, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "options/base_options.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "util/statistics_registry.h"

using namespace std;

namespace cvc5::internal {

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
    case Resource::ArithNlCoveringStep: return "ArithNlCoveringStep";
    case Resource::ArithNlLemmaStep: return "ArithNlLemmaStep";
    case Resource::BitblastStep: return "BitblastStep";
    case Resource::BvSatStep: return "BvSatStep";
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
    case Resource::SygusCheckStep: return "SygusCheckStep";
    case Resource::TheoryCheckStep: return "TheoryCheckStep";
    default: return "?Resource?";
  }
}
std::ostream& operator<<(std::ostream& os, Resource r)
{
  return os << toString(r);
}

struct ResourceManager::Statistics
{
  ReferenceStat<uint64_t> d_resourceUnitsUsed;
  IntStat d_spendResourceCalls;
  HistogramStat<theory::InferenceId> d_inferenceIdSteps;
  HistogramStat<Resource> d_resourceSteps;
  Statistics(StatisticsRegistry& stats);
};

ResourceManager::Statistics::Statistics(StatisticsRegistry& stats)
    : d_resourceUnitsUsed(
        stats.registerReference<uint64_t>("resource::resourceUnitsUsed")),
      d_spendResourceCalls(stats.registerInt("resource::spendResourceCalls")),
      d_inferenceIdSteps(stats.registerHistogram<theory::InferenceId>(
          "resource::steps::inference-id")),
      d_resourceSteps(
          stats.registerHistogram<Resource>("resource::steps::resource"))
{
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
  using theory::toString;
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

ResourceManager::ResourceManager(StatisticsRegistry& stats,
                                 const Options& options)
    : d_options(options),
      d_enabled(true),
      d_perCallTimer(),
      d_cumulativeTimeUsed(0),
      d_cumulativeResourceUsed(0),
      d_thisCallResourceUsed(0),
      d_thisCallResourceBudget(0),
      d_statistics(new ResourceManager::Statistics(stats))
{
  d_statistics->d_resourceUnitsUsed.set(d_cumulativeResourceUsed);

  d_infidWeights.fill(1);
  d_resourceWeights.fill(1);
  for (const auto& opt : d_options.base.resourceWeightHolder)
  {
    std::string name;
    uint64_t weight;
    if (parseOption(opt, name, weight))
    {
      if (setWeight<theory::InferenceId>(name, weight, d_infidWeights))
        continue;
      if (setWeight<Resource>(name, weight, d_resourceWeights)) continue;
      throw OptionException("Did not recognize resource type " + name);
    }
  }
}

ResourceManager::~ResourceManager() {}

uint64_t ResourceManager::getResourceUsage() const
{
  return d_cumulativeResourceUsed;
}

uint64_t ResourceManager::getTimeUsage() const { return d_cumulativeTimeUsed; }

uint64_t ResourceManager::getRemainingTime() const
{
  return d_options.base.perCallMillisecondLimit - d_perCallTimer.elapsed();
}

uint64_t ResourceManager::getResourceRemaining() const
{
  if (d_options.base.cumulativeResourceLimit <= d_cumulativeResourceUsed)
    return 0;
  return d_options.base.cumulativeResourceLimit - d_cumulativeResourceUsed;
}

void ResourceManager::spendResource(uint64_t amount)
{
  ++d_statistics->d_spendResourceCalls;
  d_cumulativeResourceUsed += amount;

  Trace("limit") << "ResourceManager::spendResource()" << std::endl;
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
  d_statistics->d_resourceSteps << r;
  spendResource(d_resourceWeights[i]);
}

void ResourceManager::spendResource(theory::InferenceId iid)
{
  std::size_t i = static_cast<std::size_t>(iid);
  Assert(d_infidWeights.size() > i);
  d_statistics->d_inferenceIdSteps << iid;
  spendResource(d_infidWeights[i]);
}

void ResourceManager::beginCall()
{
  // refresh here if not already done so
  refresh();
  // begin call
  d_perCallTimer.set(d_options.base.perCallMillisecondLimit);
  d_thisCallResourceUsed = 0;

  if (d_options.base.cumulativeResourceLimit > 0)
  {
    // Compute remaining cumulative resource budget
    d_thisCallResourceBudget =
        d_options.base.cumulativeResourceLimit - d_cumulativeResourceUsed;
  }
  if (d_options.base.perCallResourceLimit > 0)
  {
    // Check if per-call resource budget is even smaller
    if (d_options.base.perCallResourceLimit < d_thisCallResourceBudget)
    {
      d_thisCallResourceBudget = d_options.base.perCallResourceLimit;
    }
  }
}

void ResourceManager::refresh()
{
  d_cumulativeTimeUsed += d_perCallTimer.elapsed();
  d_perCallTimer.set(0);
  d_thisCallResourceUsed = 0;
}

bool ResourceManager::limitOn() const
{
  return (d_options.base.cumulativeResourceLimit > 0)
         || (d_options.base.perCallMillisecondLimit > 0)
         || (d_options.base.perCallResourceLimit > 0);
}

bool ResourceManager::outOfResources() const
{
  if (!d_enabled)
  {
    return false;
  }
  if (d_options.base.perCallResourceLimit > 0)
  {
    // Check if per-call resources are exhausted
    if (d_thisCallResourceUsed >= d_options.base.perCallResourceLimit)
    {
      return true;
    }
  }
  if (d_options.base.cumulativeResourceLimit > 0)
  {
    // Check if cumulative resources are exhausted
    if (d_cumulativeResourceUsed >= d_options.base.cumulativeResourceLimit)
    {
      return true;
    }
  }
  return false;
}

bool ResourceManager::outOfTime() const
{
  if (!d_enabled)
  {
    return false;
  }
  if (d_options.base.perCallMillisecondLimit == 0) return false;
  return d_perCallTimer.expired();
}

void ResourceManager::registerListener(Listener* listener)
{
  return d_listeners.push_back(listener);
}

}  // namespace cvc5::internal
