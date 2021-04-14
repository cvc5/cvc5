/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for non-linear arithmetic.
 */

#include "theory/arith/nl/stats.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

NlStats::NlStats()
    : d_mbrRuns(smtStatisticsRegistry().registerInt("nl::mbrRuns")),
      d_checkRuns(smtStatisticsRegistry().registerInt("nl::checkRuns"))
{
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
