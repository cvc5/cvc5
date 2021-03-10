/*********************                                                        */
/*! \file stats_timer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Timer statistics
 **
 ** Stat classes that hold timers
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__UTIL__STATS_TIMER_H
#define CVC4__UTIL__STATS_TIMER_H

#include <chrono>

#include "util/stats_base.h"

namespace CVC4 {
namespace timer_stat_detail {
  using clock = std::chrono::steady_clock;
  using time_point = clock::time_point;
  using duration = std::chrono::nanoseconds;
}

/**
 * Prints a timespec.
 *
 * This is used in the implementation of TimerStat. This needs to be available
 * before Stat due to ordering constraints in clang for TimerStat.
 */
std::ostream& operator<<(std::ostream& os, const timespec& t) CVC4_PUBLIC;

std::ostream& operator<<(std::ostream& os, const timer_stat_detail::duration& dur) CVC4_PUBLIC;

template <>
void CVC4_PUBLIC safe_print(int fd, const timer_stat_detail::duration& t);

class CodeTimer;

/**
 * A timer statistic.  The timer can be started and stopped
 * arbitrarily, like a stopwatch; the value of the statistic at the
 * end is the accumulated time over all (start,stop) pairs.
 */
class CVC4_PUBLIC TimerStat : public BackedStat<timer_stat_detail::duration> {

  /** The last start time of this timer */
  timer_stat_detail::time_point d_start;

  /** Whether this timer is currently running */
  bool d_running;

public:

  typedef CVC4::CodeTimer CodeTimer;

  /**
   * Construct a timer statistic with the given name.  Newly-constructed
   * timers have a 0.0 value and are not running.
   */
  TimerStat(const std::string& name)
      : BackedStat<timer_stat_detail::duration>(name, timer_stat_detail::duration()), d_start(), d_running(false) {}

  /** Start the timer. */
  void start();

  /**
   * Stop the timer and update the statistic value with the
   * accumulated time.
   */
  void stop();

  /** If the timer is currently running */
  bool running() const;

  timer_stat_detail::duration getData() const;

  void flushInformation(std::ostream& out) const override;
  void safeFlushInformation(int fd) const override;

  SExpr getValue() const override;

};/* class TimerStat */

/**
 * Utility class to make it easier to call stop() at the end of a
 * code block.  When constructed, it starts the timer.  When
 * destructed, it stops the timer.
 */
class CodeTimer {
  TimerStat& d_timer;
  bool d_reentrant;

  /** Private copy constructor undefined (no copy permitted). */
  CodeTimer(const CodeTimer& timer) = delete;
  /** Private assignment operator undefined (no copy permitted). */
  CodeTimer& operator=(const CodeTimer& timer) = delete;

public:
  CodeTimer(TimerStat& timer, bool allow_reentrant = false);
  ~CodeTimer();
};/* class CodeTimer */

}

#endif
