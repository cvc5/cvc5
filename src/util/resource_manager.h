/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner, Liana Hadarean
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

#include "cvc5_public.h"

#ifndef CVC5__RESOURCE_MANAGER_H
#define CVC5__RESOURCE_MANAGER_H

#include <stdint.h>

#include <array>
#include <chrono>
#include <memory>
#include <vector>

#include "theory/inference_id.h"

namespace cvc5::internal {

class Listener;
class Options;
class StatisticsRegistry;

/**
 * This class implements a easy to use wall clock timer based on std::chrono.
 */
class WallClockTimer
{
  /**
   * The underlying clock that is used.
   * std::chrono::system_clock represents wall clock time.
   */
  using clock = std::chrono::system_clock;
  /** A time point of the clock we use. */
  using time_point = std::chrono::time_point<clock>;

 public:
  /** Checks whether this timer is active. */
  bool on() const;
  /**
   * Activates this timer with a timeout in milliseconds.
   * If millis is zero, the timer is deactivated.
   */
  void set(uint64_t millis);
  /** Returns the number of elapsed milliseconds since the last call to set().
   */
  uint64_t elapsed() const;
  /** Checks whether the current timeout has expired. */
  bool expired() const;

 private:
  /** The start of this timer. */
  time_point d_start;
  /** The point in time when this timer expires. */
  time_point d_limit;
};

/** Types of resources. */
enum class Resource
{
  ArithPivotStep,
  ArithNlCoveringStep,
  ArithNlLemmaStep,
  BitblastStep,
  BvSatStep,
  CnfStep,
  DecisionStep,
  LemmaStep,
  NewSkolemStep,
  ParseStep,
  PreprocessStep,
  QuantifierStep,
  RestartStep,
  RewriteStep,
  SatConflictStep,
  SygusCheckStep,
  TheoryCheckStep,
  Unknown
};

const char* toString(Resource r);
std::ostream& operator<<(std::ostream& os, Resource r);

namespace resman_detail {
/** The upper bound of values from the theory::InferenceId enum */
constexpr std::size_t InferenceIdMax =
    static_cast<std::size_t>(theory::InferenceId::UNKNOWN);
/** The upper bound of values from the Resource enum */
constexpr std::size_t ResourceMax = static_cast<std::size_t>(Resource::Unknown);
};  // namespace resman_detail

/**
 * This class manages resource limits (cumulative or per call) and (per call)
 * time limits. The available resources are listed in Resource and their individual
 * costs are configured via command line options.
 */
class ResourceManager
{
 public:
  /** Construct a resource manager. */
  ResourceManager(StatisticsRegistry& statistics_registry,
                  const Options& options);
  /** Default destructor. */
  ~ResourceManager();
  /** Can not be copied. */
  ResourceManager(const ResourceManager&) = delete;
  /** Can not be moved. */
  ResourceManager(ResourceManager&&) = delete;
  /** Can not be copied. */
  ResourceManager& operator=(const ResourceManager&) = delete;
  /** Can not be moved. */
  ResourceManager& operator=(ResourceManager&&) = delete;

  void setEnabled(bool enabled) { d_enabled = enabled; }

  /** Checks whether any limit is active. */
  bool limitOn() const;

  /** Checks whether resources have been exhausted. */
  bool outOfResources() const;
  /** Checks whether time has been exhausted. */
  bool outOfTime() const;
  /** Checks whether any limit has been exhausted. */
  bool out() const { return outOfResources() || outOfTime(); }

  /** Retrieves amount of resources used overall. */
  uint64_t getResourceUsage() const;
  /** Retrieves time used over all calls. */
  uint64_t getTimeUsage() const;
  /** Retrieves the remaining time until the time limit is reached. */
  uint64_t getRemainingTime() const;
  /** Retrieves the remaining number of cumulative resources. */
  uint64_t getResourceRemaining() const;

  /**
   * Spends a given resource. Calls the listener to interrupt the solver if
   * there are no remaining resources.
   */
  void spendResource(Resource r);
  /**
   * Spends a given resource. Calls the listener to interrupt the solver if
   * there are no remaining resources.
   */
  void spendResource(theory::InferenceId iid);

  /**
   * Resets perCall limits to mark the start of a new call,
   * updates budget for current call and starts the timer
   */
  void beginCall();

  /**
   * Marks the end of a SolverEngine check call, stops the per
   * call timer.
   */
  void refresh();

  /**
   * Registers a listener that is notified on a resource out or (per-call)
   * timeout.
   */
  void registerListener(Listener* listener);

 private:
  const Options& d_options;

  /**
   * If the resource manager is not enabled, then the checks whether we are out
   * of resources are disabled. Resources are still spent, however.
   */
  bool d_enabled;

  /** The per-call wall clock timer. */
  WallClockTimer d_perCallTimer;

  /** The total number of milliseconds used. */
  uint64_t d_cumulativeTimeUsed;
  /** The total amount of resources used. */
  uint64_t d_cumulativeResourceUsed;

  /** The amount of resources used during this call. */
  uint64_t d_thisCallResourceUsed;

  /**
   * The resource budget for this call (min between per call
   * budget and left-over cumulative budget.)
   */
  uint64_t d_thisCallResourceBudget;

  /** Receives a notification on reaching a limit. */
  std::vector<Listener*> d_listeners;

  void spendResource(uint64_t amount);

  /** Weights for InferenceId resources */
  std::array<uint64_t, resman_detail::InferenceIdMax + 1> d_infidWeights;
  /** Weights for Resource resources */
  std::array<uint64_t, resman_detail::ResourceMax + 1> d_resourceWeights;

  struct Statistics;
  /** The statistics object */
  std::unique_ptr<Statistics> d_statistics;
}; /* class ResourceManager */

}  // namespace cvc5::internal

#endif /* CVC5__RESOURCE_MANAGER_H */
