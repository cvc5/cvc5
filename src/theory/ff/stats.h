/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields stats
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__STATS_H
#define CVC5__THEORY__FF__STATS_H

#include <string>

#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

struct FfStatistics
{
  /**
   * Number of runs of the GB engine for reasoning.
   * Excludes calls to the GB engine for model construction.
   */
  IntStat d_numGbRuns;
  /**
   * Time spent in Groebner-basis reductions
   */
  TimerStat d_reductionTime;
  /**
   * Number of reductions where 1 was in the original ideal.
   * I.e. the number of times that the ideal was trivially unsat.
   */
  IntStat d_numTrivialUnsat;
  /**
   * Time spent in model construction
   */
  TimerStat d_modelConstructionTime;
  /**
   * Number of times that model construction gave an error
   */
  IntStat d_numConstructionErrors;
  /**
   * Number of times the ideal was zero dimensional.
   */
  IntStat d_idealMinPoly;
  /**
   * Number of times the ideal was positive dimensional.
   */
  IntStat d_idealPosDim;

  FfStatistics(StatisticsRegistry& reg, const std::string& prefix);
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__STATS_H */
