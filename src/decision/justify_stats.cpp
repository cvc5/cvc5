/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justification stats.
 */

#include "decision/justify_stats.h"

namespace cvc5::internal {
namespace decision {

JustifyStatistics::JustifyStatistics()
    : d_numStatusNoDecision(
        statisticsRegistry().registerInt("JustifyStrategy::StatusNoDecision")),
      d_numStatusDecision(
          statisticsRegistry().registerInt("JustifyStrategy::StatusDecision")),
      d_numStatusBacktrack(
          statisticsRegistry().registerInt("JustifyStrategy::StatusBacktrack")),
      d_maxStackSize(
          statisticsRegistry().registerInt("JustifyStrategy::MaxStackSize")),
      d_maxAssertionsSize(statisticsRegistry().registerInt(
          "JustifyStrategy::MaxAssertionsSize")),
      d_maxSkolemDefsSize(statisticsRegistry().registerInt(
          "JustifyStrategy::MaxSkolemDefsSize"))
{
}

JustifyStatistics::~JustifyStatistics() {}

}
}  // namespace cvc5::internal
