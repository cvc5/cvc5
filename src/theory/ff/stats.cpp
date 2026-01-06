/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields statistics
 */

#include "theory/ff/stats.h"

#include "base/output.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

FfStatistics::FfStatistics(StatisticsRegistry& reg, const std::string& prefix)
    : d_numReductions(reg.registerInt(prefix + "num_reductions")),
      d_reductionTime(reg.registerTimer(prefix + "reduction_time")),
      d_numTrivialUnsat(reg.registerInt(prefix + "num_trivial_unsat")),
      d_modelConstructionTime(
          reg.registerTimer(prefix + "model_construction_time")),
      d_numConstructionErrors(
          reg.registerInt(prefix + "num_construction_errors")),
      d_idealMinPoly(reg.registerInt(prefix + "num_ideal_min_poly")),
      d_idealPosDim(reg.registerInt(prefix + "num_ideal_pos_dim"))
{
  Trace("ff::stats") << "ff registered stats" << std::endl;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
