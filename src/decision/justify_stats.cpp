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

#include "decision/justify_stats.h"

namespace cvc5::internal {
namespace decision {

JustifyStatistics::JustifyStatistics(StatisticsRegistry& sr)
    : d_numStatusNoDecision(
        sr.registerInt("JustifyStrategy::StatusNoDecision")),
      d_numStatusDecision(sr.registerInt("JustifyStrategy::StatusDecision")),
      d_numStatusBacktrack(sr.registerInt("JustifyStrategy::StatusBacktrack")),
      d_maxStackSize(sr.registerInt("JustifyStrategy::MaxStackSize")),
      d_maxAssertionsSize(sr.registerInt("JustifyStrategy::MaxAssertionsSize")),
      d_maxSkolemDefsSize(sr.registerInt("JustifyStrategy::MaxSkolemDefsSize"))
{
}

JustifyStatistics::~JustifyStatistics() {}

}
}  // namespace cvc5::internal
