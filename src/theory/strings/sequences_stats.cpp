/*********************                                                        */
/*! \file sequences_stats.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for the theory of strings/sequences
 **/


#include "theory/strings/sequences_stats.h"

#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace strings {

SequencesStatistics::SequencesStatistics()
    : d_inferences("theory::strings::inferences"),
      d_reductions("theory::strings::reductions"),
      d_conflictsEqEngine("theory::strings::conflictsEqEngine", 0),
      d_conflictsEagerPrefix("theory::strings::conflictsEagerPrefix", 0),
      d_conflictsInfer("theory::strings::conflictsInfer", 0),
      d_lemmaEagerPreproc("theory::strings::lemmaEagerPreproc", 0),
      d_lemmaCmiSplit("theory::strings::lemmaCmiSplit", 0),
      d_lemmaRegisterTerm("theory::strings::lemmaRegisterTerm", 0),
      d_lemmaRegisterTermAtomic("theory::strings::lemmaRegisterTermAtomic", 0),
      d_lemmaInfer("theory::strings::lemmaInfer", 0)
{
  smtStatisticsRegistry()->registerStat(&d_inferences);
  smtStatisticsRegistry()->registerStat(&d_reductions);
  smtStatisticsRegistry()->registerStat(&d_conflictsEqEngine);
  smtStatisticsRegistry()->registerStat(&d_conflictsEagerPrefix);
  smtStatisticsRegistry()->registerStat(&d_conflictsInfer);
  smtStatisticsRegistry()->registerStat(&d_lemmaEagerPreproc);
  smtStatisticsRegistry()->registerStat(&d_lemmaCmiSplit);
  smtStatisticsRegistry()->registerStat(&d_lemmaRegisterTerm);
  smtStatisticsRegistry()->registerStat(&d_lemmaRegisterTermAtomic);
  smtStatisticsRegistry()->registerStat(&d_lemmaInfer);
}

SequencesStatistics::~SequencesStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_inferences);
  smtStatisticsRegistry()->unregisterStat(&d_reductions);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsEqEngine);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsEagerPrefix);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsInfer);
  smtStatisticsRegistry()->unregisterStat(&d_lemmaEagerPreproc);
  smtStatisticsRegistry()->unregisterStat(&d_lemmaCmiSplit);
  smtStatisticsRegistry()->unregisterStat(&d_lemmaRegisterTerm);
  smtStatisticsRegistry()->unregisterStat(&d_lemmaRegisterTermAtomic);
  smtStatisticsRegistry()->unregisterStat(&d_lemmaInfer);
}

}
}
}
