/*********************                                                        */
/*! \file sequences_stats.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for the theory of strings/sequences
 **/

#include "theory/strings/sequences_stats.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5 {
namespace theory {
namespace strings {

SequencesStatistics::SequencesStatistics()
    : d_checkRuns("theory::strings::checkRuns", 0),
      d_strategyRuns("theory::strings::strategyRuns", 0),
      d_inferencesNoPf("theory::strings::inferencesNoPf"),
      d_cdSimplifications("theory::strings::cdSimplifications"),
      d_reductions("theory::strings::reductions"),
      d_regexpUnfoldingsPos("theory::strings::regexpUnfoldingsPos"),
      d_regexpUnfoldingsNeg("theory::strings::regexpUnfoldingsNeg"),
      d_rewrites("theory::strings::rewrites"),
      d_conflictsEqEngine("theory::strings::conflictsEqEngine", 0),
      d_conflictsEager("theory::strings::conflictsEager", 0),
      d_conflictsInfer("theory::strings::conflictsInfer", 0)
{
  smtStatisticsRegistry()->registerStat(&d_checkRuns);
  smtStatisticsRegistry()->registerStat(&d_strategyRuns);
  smtStatisticsRegistry()->registerStat(&d_inferencesNoPf);
  smtStatisticsRegistry()->registerStat(&d_cdSimplifications);
  smtStatisticsRegistry()->registerStat(&d_reductions);
  smtStatisticsRegistry()->registerStat(&d_regexpUnfoldingsPos);
  smtStatisticsRegistry()->registerStat(&d_regexpUnfoldingsNeg);
  smtStatisticsRegistry()->registerStat(&d_rewrites);
  smtStatisticsRegistry()->registerStat(&d_conflictsEqEngine);
  smtStatisticsRegistry()->registerStat(&d_conflictsEager);
  smtStatisticsRegistry()->registerStat(&d_conflictsInfer);
}

SequencesStatistics::~SequencesStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_checkRuns);
  smtStatisticsRegistry()->unregisterStat(&d_strategyRuns);
  smtStatisticsRegistry()->unregisterStat(&d_inferencesNoPf);
  smtStatisticsRegistry()->unregisterStat(&d_cdSimplifications);
  smtStatisticsRegistry()->unregisterStat(&d_reductions);
  smtStatisticsRegistry()->unregisterStat(&d_regexpUnfoldingsPos);
  smtStatisticsRegistry()->unregisterStat(&d_regexpUnfoldingsNeg);
  smtStatisticsRegistry()->unregisterStat(&d_rewrites);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsEqEngine);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsEager);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsInfer);
}

}
}
}  // namespace cvc5
