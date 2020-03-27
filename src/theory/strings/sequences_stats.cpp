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
      d_lemmasEagerPreproc("theory::strings::lemmasEagerPreproc", 0),
      d_lemmasCmiSplit("theory::strings::lemmasCmiSplit", 0),
      d_lemmasRegisterTerm("theory::strings::lemmasRegisterTerm", 0),
      d_lemmasRegisterTermAtomic("theory::strings::lemmasRegisterTermAtomic",
                                 0),
      d_lemmasInfer("theory::strings::lemmasInfer", 0)
{
  smtStatisticsRegistry()->registerStat(&d_inferences);
  smtStatisticsRegistry()->registerStat(&d_reductions);
  smtStatisticsRegistry()->registerStat(&d_conflictsEqEngine);
  smtStatisticsRegistry()->registerStat(&d_conflictsEagerPrefix);
  smtStatisticsRegistry()->registerStat(&d_conflictsInfer);
  smtStatisticsRegistry()->registerStat(&d_lemmasEagerPreproc);
  smtStatisticsRegistry()->registerStat(&d_lemmasCmiSplit);
  smtStatisticsRegistry()->registerStat(&d_lemmasRegisterTerm);
  smtStatisticsRegistry()->registerStat(&d_lemmasRegisterTermAtomic);
  smtStatisticsRegistry()->registerStat(&d_lemmasInfer);
}

SequencesStatistics::~SequencesStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_inferences);
  smtStatisticsRegistry()->unregisterStat(&d_reductions);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsEqEngine);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsEagerPrefix);
  smtStatisticsRegistry()->unregisterStat(&d_conflictsInfer);
  smtStatisticsRegistry()->unregisterStat(&d_lemmasEagerPreproc);
  smtStatisticsRegistry()->unregisterStat(&d_lemmasCmiSplit);
  smtStatisticsRegistry()->unregisterStat(&d_lemmasRegisterTerm);
  smtStatisticsRegistry()->unregisterStat(&d_lemmasRegisterTermAtomic);
  smtStatisticsRegistry()->unregisterStat(&d_lemmasInfer);
}

}
}
}
