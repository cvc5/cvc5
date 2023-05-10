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
 * Statistics for non-linear arithmetic.
 */

#include "theory/arith/nl/stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

NlStats::NlStats(StatisticsRegistry& sr)
    : d_mbrRuns(sr.registerInt("nl::mbrRuns")),
      d_checkRuns(sr.registerInt("nl::checkRuns"))
{
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
