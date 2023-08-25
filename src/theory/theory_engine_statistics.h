/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory engine statistics class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_ENGINE_STATISTICS_H
#define CVC5__THEORY__THEORY_ENGINE_STATISTICS_H

#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {

/**
 * Statistics class for theory engine, which contains all statistics that need
 * to be tracked globally within the theory engine.
 */
class TheoryEngineStatistics
{
 public:
  TheoryEngineStatistics(StatisticsRegistry& sr);
  /** Time spent in theory combination */
  TimerStat d_combineTheoriesTime;
  /** Number of standard effort checks */
  IntStat d_stdEffortChecks;
  /** Number of full effort checks */
  IntStat d_fullEffortChecks;
  /** Number of calls to combineTheories */
  IntStat d_combineTheoriesCalls;
  /** Number of last call effort checks */
  IntStat d_lcEffortChecks;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__THEORY_ENGINE_STATISTICS_H */
