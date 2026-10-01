/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for RAII-style measurement of the wall-clock time of a scope.
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__SCOPED_TIMER_H
#define CVC5__UTIL__SCOPED_TIMER_H

#include <chrono>
#include <cstdint>

namespace cvc5::internal {

/**
 * Measures the wall-clock time of a scope. The timer starts when constructed.
 * When destructed, the number of elapsed milliseconds is written to the
 * reference given on construction.
 *
 * In contrast to `TimerStat::CodeTimer`, this does not require a registered
 * statistic, and is intended for code whose behavior depends on the measured
 * time.
 */
class ScopedTimer
{
 public:
  /**
   * Start the timer.
   * @param millis Reference to write the elapsed milliseconds to on
   * destruction.
   */
  explicit ScopedTimer(uint64_t& millis)
      : d_millis(millis), d_start(std::chrono::steady_clock::now())
  {
  }
  /** Disallow copying */
  ScopedTimer(const ScopedTimer&) = delete;
  /** Disallow assignment */
  ScopedTimer& operator=(const ScopedTimer&) = delete;
  /** Stop the timer and write the elapsed milliseconds. */
  ~ScopedTimer() { d_millis = elapsed(); }
  /** Returns the number of milliseconds elapsed since construction. */
  uint64_t elapsed() const
  {
    return std::chrono::duration_cast<std::chrono::milliseconds>(
               std::chrono::steady_clock::now() - d_start)
        .count();
  }

 private:
  /** Reference to write the elapsed milliseconds to */
  uint64_t& d_millis;
  /** The start of this timer */
  std::chrono::steady_clock::time_point d_start;
};

}  // namespace cvc5::internal

#endif /* CVC5__UTIL__SCOPED_TIMER_H */
