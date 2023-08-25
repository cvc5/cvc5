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
 * Theory engine statistics class.
 */

#include "theory/theory_engine_statistics.h"

namespace cvc5::internal {
namespace theory {

TheoryEngineStatistics::TheoryEngineStatistics(StatisticsRegistry& sr)
    : d_combineTheoriesTime(
        sr.registerTimer("TheoryEngine::combineTheoriesTime")),
      d_stdEffortChecks(sr.registerInt("TheoryEngine::Checks_Standard")),
      d_fullEffortChecks(sr.registerInt("TheoryEngine::Checks_Full")),
      d_combineTheoriesCalls(
          sr.registerInt("TheoryEngine::combineTheoriesCalls")),
      d_lcEffortChecks(sr.registerInt("TheoryEngine::Checks_Last_Call"))
{
}

}  // namespace theory
}  // namespace cvc5::internal
