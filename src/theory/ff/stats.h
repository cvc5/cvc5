/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
   * Number of groebner-basis reductions
   */
  IntStat d_numReductions;
  /**
   * Time spent in groebner-basis reductions
   */
  TimerStat d_reductionTime;
  /**
   * Time spent in model construction
   */
  TimerStat d_modelConstructionTime;
  /**
   * Number of times that model construction gave an error
   */
  IntStat d_numConstructionErrors;

  FfStatistics(StatisticsRegistry& reg, const std::string& prefix);
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__STATS_H */
