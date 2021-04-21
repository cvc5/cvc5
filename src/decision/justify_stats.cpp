/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Justification stats.
 */

#include "decision/justify_stats.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5 {
namespace decision {

JustifyStatistics::JustifyStatistics()
    : d_numStatusNoDecision(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::StatusNoDecision", 0)),
      d_numStatusDecision(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::StatusDecision", 0)),
      d_numStatusBacktrack(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::StatusBacktrack", 0)),
      d_maxStackSize(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::MaxStackSize", 0)),
      d_maxAssertionsSize(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::MaxAssertionsSize", 0)),
      d_maxSkolemDefsSize(smtStatisticsRegistry().registerInt(
          "JustifyStrategy::MaxSkolemDefsSize", 0))
{
}

JustifyStatistics::~JustifyStatistics() {}

}
}  // namespace cvc5
