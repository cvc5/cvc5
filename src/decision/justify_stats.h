/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justification stats.
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__JUSTIFY_STATS_H
#define CVC5__DECISION__JUSTIFY_STATS_H

#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace decision {

class JustifyStatistics
{
 public:
  JustifyStatistics(StatisticsRegistry& sr);
  ~JustifyStatistics();
  /** Number of times we considered an assertion not leading to a decision */
  IntStat d_numStatusNoDecision;
  /** Number of times we considered an assertion that led to a decision */
  IntStat d_numStatusDecision;
  /** Number of times we considered an assertion that led to backtracking */
  IntStat d_numStatusBacktrack;
  /** Maximum stack size we considered */
  IntStat d_maxStackSize;
  /** Maximum assertion size we considered */
  IntStat d_maxAssertionsSize;
  /** Maximum skolem definition size we considered */
  IntStat d_maxSkolemDefsSize;
};

}
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__JUSTIFY_STATS_H */
