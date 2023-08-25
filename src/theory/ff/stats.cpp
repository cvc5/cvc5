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
 * Finite fields statistics
 */

#include "theory/ff/stats.h"

#include <iostream>

#include "base/output.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

FfStatistics::FfStatistics(StatisticsRegistry& registry,
                           const std::string& prefix)
    : d_numReductions(registry.registerInt(prefix + "num_reductions")),
      d_reductionTime(registry.registerTimer(prefix + "reduction_time")),
      d_modelConstructionTime(
          registry.registerTimer(prefix + "model_construction_time")),
      d_numConstructionErrors(
          registry.registerInt(prefix + "num_construction_errors"))
{
  Trace("ff::stats") << "ff registered 4 stats" << std::endl;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
