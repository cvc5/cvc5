/*********************                                                        */
/*! \file resource_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Liana Hadarean, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Provides mechanisms to limit resources.
  **
 ** This file provides the ResourceManager class. It can be used to impose
 ** (cumulative and per-call) resource limits on the solver, as well as per-call
 ** time limits.
 **/

#include "cvc4_public.h"

#ifndef CVC4__RESOURCE_MANAGER_H
#define CVC4__RESOURCE_MANAGER_H

#include <sys/time.h>

#include <chrono>
#include <cstddef>
#include <memory>

#include "base/exception.h"
#include "base/listener.h"
#include "options/options.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {

class StatisticsRegistry;

/**
 * This class implements a easy to use wall clock timer based on std::chrono.
 */
class CVC4_PUBLIC WallClockTimer
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

/**
 * This class manages resource limits (cumulative or per call) and (per call)
 * time limits. The available resources are listed in ResourceManager::Resource
 * and their individual costs are configured via command line options.
 */
class CVC4_PUBLIC ResourceManager
{
 public:
  /** Types of resources. */
  enum class Resource
  {
    BitblastStep,
    BvEagerAssertStep,
    BvPropagationStep,
    BvSatConflictsStep,
    CnfStep,
    DecisionStep,
    LemmaStep,
    ParseStep,
    PreprocessStep,
    QuantifierStep,
    RestartStep,
    RewriteStep,
    SatConflictStep,
    TheoryCheckStep,
  };

  /** Construst a resource manager. */
  ResourceManager(StatisticsRegistry& statistics_registry, Options& options);
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

  /** Checks whether any limit is active. */
  bool limitOn() const { return cumulativeLimitOn() || perCallLimitOn(); }
  /** Checks whether any cumulative limit is active. */
  bool cumulativeLimitOn() const;
  /** Checks whether any per-call limit is active. */
  bool perCallLimitOn() const;

  /** Checks whether resources have been exhausted. */
  bool outOfResources() const;
  /** Checks whether time has been exhausted. */
  bool outOfTime() const;
  /** Checks whether any limit has been exhausted. */
  bool out() const { return d_on && (outOfResources() || outOfTime()); }

  /** Retrieves amount of resources used overall. */
  uint64_t getResourceUsage() const;
  /** Retrieves time used over all calls. */
  uint64_t getTimeUsage() const;
  /** Retrieves the remaining number of cumulative resources. */
  uint64_t getResourceRemaining() const;

  /** Retrieves resource budget for this call. */
  uint64_t getResourceBudgetForThisCall() { return d_thisCallResourceBudget; }

  /**
   * Spends a given resources. Throws an UnsafeInterruptException if there are
   * no remaining resources.
   */
  void spendResource(Resource r);

  /** Sets the resource limit. */
  void setResourceLimit(uint64_t units, bool cumulative = false);
  /** Sets the time limit. */
  void setTimeLimit(uint64_t millis);
  /** Sets whether resource limitation is enabled. */
  void enable(bool on);

  /**
   * Resets perCall limits to mark the start of a new call,
   * updates budget for current call and starts the timer
   */
  void beginCall();

  /**
   * Marks the end of a SmtEngine check call, stops the per
   * call timer.
   */
  void endCall();

  static uint64_t getFrequencyCount() { return s_resourceCount; }

  /**
   * Registers a listener that is notified on a resource out or (per-call)
   * timeout.
   */
  void registerListener(Listener* listener);

 private:
  /** The per-call wall clock timer. */
  WallClockTimer d_perCallTimer;

  /** A user-imposed per-call time budget, in milliseconds. 0 = no limit. */
  uint64_t d_timeBudgetPerCall;
  /** A user-imposed cumulative resource budget. 0 = no limit. */
  uint64_t d_resourceBudgetCumulative;
  /** A user-imposed per-call resource budget. 0 = no limit. */
  uint64_t d_resourceBudgetPerCall;

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

  /** A flag indicating whether resource limitation is active. */
  bool d_on;

  /** Counter indicating how often to check resource manager in loops */
  static const uint64_t s_resourceCount;

  /** Receives a notification on reaching a limit. */
  std::vector<Listener*> d_listeners;

  void spendResource(unsigned amount);

  struct Statistics;
  std::unique_ptr<Statistics> d_statistics;

  Options& d_options;

}; /* class ResourceManager */

}  // namespace CVC4

#endif /* CVC4__RESOURCE_MANAGER_H */
