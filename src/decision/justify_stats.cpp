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

#include "smt/smt_statistics_registry.h"

namespace cvc5::internal {
namespace decision {

JustifyStatistics::JustifyStatistics()
    : d_numStatusNoDecision(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::StatusNoDecision")),
      d_numStatusDecision(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::StatusDecision")),
      d_numStatusBacktrack(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::StatusBacktrack")),
      d_maxStackSize(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::MaxStackSize")),
      d_maxAssertionsSize(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::MaxAssertionsSize")),
      d_maxSkolemDefsSize(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::MaxSkolemDefsSize"))
{
}

JustifyStatistics::~JustifyStatistics() {}

}
}  // namespace cvc5::internal
