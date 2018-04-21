/*********************                                                        */
/*! \file resource_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "cvc4_public.h"

#ifndef __CVC4__RESOURCE_MANAGER_H
#define __CVC4__RESOURCE_MANAGER_H

#include <cstddef>
#include <sys/time.h>

#include "base/exception.h"
#include "base/listener.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {

/**
 * A helper class to keep track of a time budget and signal
 * the PropEngine when the budget expires.
 */
class CVC4_PUBLIC Timer {
 public:
  /** Construct a Timer. */
  Timer()
      : d_ms(0),
        d_cpu_start_time(0),
        d_cpu_limit(0),
        d_wall_time(true)
  {
    d_wall_limit.tv_sec = 0;
    d_wall_limit.tv_usec = 0;
  }

  /** Is the timer currently active? */
  bool on() const {
    return d_ms != 0;
  }

  /** Set a millisecond timer (0==off). */
  void set(uint64_t millis, bool wall_time = true);
  /** Return the milliseconds elapsed since last set() wall/cpu time
   depending on d_wall_time*/
  uint64_t elapsed() const;
  bool expired() const;

 private:

  /** Return the milliseconds elapsed since last set() cpu time. */
  uint64_t elapsedCPU() const;
  /** Return the milliseconds elapsed since last set() wall time. */
  uint64_t elapsedWall() const;

  uint64_t d_ms;
  clock_t d_cpu_start_time;
  clock_t d_cpu_limit;
  bool d_wall_time;
  timeval d_wall_limit;
};/* class Timer */


class CVC4_PUBLIC ResourceManager {

  Timer d_cumulativeTimer;
  Timer d_perCallTimer;

  /** A user-imposed cumulative time budget, in milliseconds. 0 = no limit. */
  uint64_t d_timeBudgetCumulative;
  /** A user-imposed per-call time budget, in milliseconds. 0 = no limit. */
  uint64_t d_timeBudgetPerCall;
  /** A user-imposed cumulative resource budget. 0 = no limit. */
  uint64_t d_resourceBudgetCumulative;
  /** A user-imposed per-call resource budget. 0 = no limit. */
  uint64_t d_resourceBudgetPerCall;

  /** The number of milliseconds used. */
  uint64_t d_cumulativeTimeUsed;
  /** The amount of resource used. */
  uint64_t d_cumulativeResourceUsed;

  /** The amount of resource used during this call. */
  uint64_t d_thisCallResourceUsed;

  /**
   * The amount of resource budget for this call (min between per call
   * budget and left-over cumulative budget.
   */
  uint64_t d_thisCallTimeBudget;
  uint64_t d_thisCallResourceBudget;

  bool d_isHardLimit;
  bool d_on;
  bool d_cpuTime;
  uint64_t d_spendResourceCalls;

  /** Counter indicating how often to check resource manager in loops */
  static const uint64_t s_resourceCount;

  /** Receives a notification on reaching a hard limit. */
  ListenerCollection d_hardListeners;

  /** Receives a notification on reaching a hard limit. */
  ListenerCollection d_softListeners;

  /**
   * ResourceManagers cannot be copied as they are given an explicit
   * list of Listeners to respond to.
   */
  ResourceManager(const ResourceManager&) CVC4_UNDEFINED;

  /**
   * ResourceManagers cannot be assigned as they are given an explicit
   * list of Listeners to respond to.
   */
  ResourceManager& operator=(const ResourceManager&) CVC4_UNDEFINED;

public:

  ResourceManager();

  bool limitOn() const { return cumulativeLimitOn() || perCallLimitOn(); }
  bool cumulativeLimitOn() const;
  bool perCallLimitOn() const;

  bool outOfResources() const;
  bool outOfTime() const;
  bool out() const { return d_on && (outOfResources() || outOfTime()); }


  /**
   * This returns a const uint64_t& to support being used as a ReferenceStat.
   */
  const uint64_t& getResourceUsage() const;
  uint64_t getTimeUsage() const;
  uint64_t getResourceRemaining() const;
  uint64_t getTimeRemaining() const;

  uint64_t getResourceBudgetForThisCall() {
    return d_thisCallResourceBudget;
  }
  // Throws an UnsafeInterruptException if there are no remaining resources.
  void spendResource(unsigned amount);

  void setHardLimit(bool value);
  void setResourceLimit(uint64_t units, bool cumulative = false);
  void setTimeLimit(uint64_t millis, bool cumulative = false);
  void useCPUTime(bool cpu);

  void enable(bool on);

  /**
   * Resets perCall limits to mark the start of a new call,
   * updates budget for current call and starts the timer
   */
  void beginCall();

  /**
   * Marks the end of a SmtEngine check call, stops the per
   * call timer, updates cumulative time used.
   */
  void endCall();

  static uint64_t getFrequencyCount() { return s_resourceCount; }

  /**
   * Registers a listener that is notified on a hard resource out.
   *
   * This Registration must be destroyed by the user before this
   * ResourceManager.
   */
  ListenerCollection::Registration* registerHardListener(Listener* listener);

  /**
   * Registers a listener that is notified on a soft resource out.
   *
   * This Registration must be destroyed by the user before this
   * ResourceManager.
   */
  ListenerCollection::Registration* registerSoftListener(Listener* listener);

};/* class ResourceManager */


}/* CVC4 namespace */

#endif /* __CVC4__RESOURCE_MANAGER_H */
