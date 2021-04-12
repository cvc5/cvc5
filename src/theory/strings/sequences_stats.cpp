/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the theory of strings/sequences.
 */

#include "theory/strings/sequences_stats.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5 {
namespace theory {
namespace strings {

SequencesStatistics::SequencesStatistics()
    : d_checkRuns(
        smtStatisticsRegistry().registerInt("theory::strings::checkRuns")),
      d_strategyRuns(
          smtStatisticsRegistry().registerInt("theory::strings::strategyRuns")),
      d_inferencesNoPf(smtStatisticsRegistry().registerHistogram<InferenceId>(
          "theory::strings::inferencesNoPf")),
      d_cdSimplifications(smtStatisticsRegistry().registerHistogram<Kind>(
          "theory::strings::cdSimplifications")),
      d_reductions(smtStatisticsRegistry().registerHistogram<Kind>(
          "theory::strings::reductions")),
      d_regexpUnfoldingsPos(smtStatisticsRegistry().registerHistogram<Kind>(
          "theory::strings::regexpUnfoldingsPos")),
      d_regexpUnfoldingsNeg(smtStatisticsRegistry().registerHistogram<Kind>(
          "theory::strings::regexpUnfoldingsNeg")),
      d_rewrites(smtStatisticsRegistry().registerHistogram<Rewrite>(
          "theory::strings::rewrites")),
      d_conflictsEqEngine(smtStatisticsRegistry().registerInt(
          "theory::strings::conflictsEqEngine")),
      d_conflictsEager(smtStatisticsRegistry().registerInt(
          "theory::strings::conflictsEager")),
      d_conflictsInfer(smtStatisticsRegistry().registerInt(
          "theory::strings::conflictsInfer"))
{
}

}
}
}  // namespace cvc5
