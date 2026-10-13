/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

#include "base/exception.h"
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
  TheoryFullCheckStep,
  FindSynthStep,
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
 * Exception thrown by the resource manager when a resource or time limit is
 * reached while the resource manager is armed to throw (see
 * ResourceManager::ThrowScope). It unwinds the solver out of any phase that
 * does not observe interrupts cooperatively, e.g. preprocessing.
 *
 * It must only be thrown when some enclosing frame catches it before it
 * reaches a frame of a third-party library (e.g. a SAT solver).
 */
class ResourceOutException : public Exception
{
 public:
  /**
   * @param timeout True if a time limit was reached, false if a resource
   * limit was reached.
   */
  ResourceOutException(bool timeout)
      : Exception(timeout ? "Time limit reached" : "Resource limit reached"),
        d_timeout(timeout)
  {
  }
  /** Was a time limit (as opposed to a resource limit) reached? */
  bool isTimeout() const { return d_timeout; }

 private:
  /** True if a time limit was reached. */
  bool d_timeout;
};

/**
 * This class manages resource limits (cumulative or per call) and (per call)
 * time limits. The available resources are listed in Resource and their
 * individual costs are configured via command line options.
 */
class ResourceManager
{
 public:
  /**
   * RAII helper that arms or disarms the resource manager for throwing a
   * ResourceOutException when a limit is reached. The previous state is
   * restored on destruction, so scopes nest.
   *
   * Arming has no effect if the option resource-limit-abort is disabled.
   */
  class ThrowScope
  {
   public:
    /**
     * @param rm The resource manager.
     * @param armed True to arm, false to disarm, for the lifetime of this
     * object.
     */
    ThrowScope(ResourceManager& rm, bool armed);
    ~ThrowScope();
    ThrowScope(const ThrowScope&) = delete;
    ThrowScope& operator=(const ThrowScope&) = delete;

   private:
    /** The resource manager */
    ResourceManager& d_rm;
    /** The state to restore */
    bool d_previous;
    /** The resource manager to restore in s_armed */
    ResourceManager* d_previousArmed;
  };

  /**
   * A cheap checkpoint for long running loops in code that runs in an armed
   * region. Unlike spendResource, this does not spend resources, so it does
   * not affect resource counts. If this resource manager is armed and a limit
   * has been reached, it notifies the listeners and throws a
   * ResourceOutException. To keep it cheap (reading the wall clock is not),
   * the limits are only consulted every few calls.
   */
  void checkLimit()
  {
    if (d_throwArmed && ((++d_checkCount) & (kCheckInterval - 1)) == 0)
    {
      checkLimitSlow();
    }
  }
  /**
   * Same as checkLimit on the resource manager that is currently armed in this
   * thread, if any. This allows placing checkpoints in code that has no access
   * to the resource manager. It is a no-op if no resource manager is armed.
   */
  static void checkpoint()
  {
    if (s_armed != nullptr)
    {
      s_armed->checkLimit();
    }
  }

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
   * there are no remaining resources. If additionally this resource manager is
   * armed (see ThrowScope), throws a ResourceOutException.
   */
  void spendResource(Resource r);
  /**
   * Gets the number of resources spent for r so far.
   */
  uint64_t getResource(Resource r) const;
  /**
   * Spends a given resource. Calls the listener to interrupt the solver if
   * there are no remaining resources. If additionally this resource manager is
   * armed (see ThrowScope), throws a ResourceOutException.
   */
  void spendResource(theory::InferenceId iid);

  /**
   * Did a ResourceOutException get thrown since the last call to beginCall()?
   * This is true even if the exception was caught and absorbed by some frame
   * before it reached the top-level check-sat call.
   */
  bool abortedThisCall() const { return d_abortedThisCall; }

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

  /**
   * Whether spending a resource throws a ResourceOutException when a limit is
   * reached. Managed by ThrowScope.
   */
  bool d_throwArmed;
  /** Was a ResourceOutException thrown since the last call to beginCall()? */
  bool d_abortedThisCall;
  /** Number of calls to checkLimit while armed, since the last beginCall(). */
  uint32_t d_checkCount;
  /** Only every kCheckInterval-th call to checkLimit consults the limits. */
  static constexpr uint32_t kCheckInterval = 64;
  /**
   * The resource manager that is currently armed in this thread, or nullptr.
   * Maintained by ThrowScope.
   */
  static thread_local ResourceManager* s_armed;

  /** Slow path of checkLimit */
  void checkLimitSlow();
  /**
   * Notify the listeners that a limit has been reached, and throw a
   * ResourceOutException if armed.
   */
  void notifyAndAbort();

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
