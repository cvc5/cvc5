/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the theory of strings/sequences.
 */

#include "theory/strings/sequences_stats.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

SequencesStatistics::SequencesStatistics(StatisticsRegistry& sr)
    : d_checkRuns(sr.registerInt("theory::strings::checkRuns")),
      d_strategyRuns(sr.registerInt("theory::strings::strategyRuns")),
      d_cdSimplifications(
          sr.registerHistogram<Kind>("theory::strings::cdSimplifications")),
      d_reductions(sr.registerHistogram<Kind>("theory::strings::reductions")),
      d_regexpUnfoldingsPos(
          sr.registerHistogram<Kind>("theory::strings::regexpUnfoldingsPos")),
      d_regexpUnfoldingsNeg(
          sr.registerHistogram<Kind>("theory::strings::regexpUnfoldingsNeg")),
      d_rewrites(sr.registerHistogram<Rewrite>("theory::strings::rewrites")),
      d_conflictsEqEngine(sr.registerInt("theory::strings::conflictsEqEngine")),
      d_conflictsEager(sr.registerInt("theory::strings::conflictsEager")),
      d_conflictsInfer(sr.registerInt("theory::strings::conflictsInfer"))
{
}

}
}
}  // namespace cvc5::internal
