/*********************                                                        */
/*! \file sequences_stats.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__SEQUENCES_STATS_H
#define CVC4__THEORY__STRINGS__SEQUENCES_STATS_H

#include "theory/strings/infer_info.h"
#include "expr/kind.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace strings {

class SequencesStatistics
{
 public:
  SequencesStatistics();
  ~SequencesStatistics();

  /** Counts the number of applications of each type of inference */
  HistogramStat<Inference> d_inferences;
  /** Counts the number of applications of each type of reduction */
  HistogramStat<Kind> d_reductions;
  //-------------------------------- types of conflicts
  /** Number of equality engine conflicts */
  IntStat d_conflictsEqEngine;
  /** Number of eager prefix conflicts */
  IntStat d_conflictsEagerPrefix;
  /** Number of inference conflicts */
  IntStat d_conflictsInfer;
  //-------------------------------- end types of conflicts
  //-------------------------------- types of lemmas
  /** Number of lemmas added due to eager preprocessing */
  IntStat d_lemmaEagerPreproc;
  /** Number of collect model info splits */
  IntStat d_lemmaCmiSplit;
  /** Number of lemmas added due to registering terms */
  IntStat d_lemmaRegisterTerm;
  /** Number of lemmas added due to registering atomic terms */
  IntStat d_lemmaRegisterTermAtomic;
  /** Number of lemmas added due to inferences */
  IntStat d_lemmaInfer;
  //-------------------------------- end of lemmas
};

}
}
}

#endif /* CVC4__THEORY__STRINGS__SEQUENCES_STATS_H */
