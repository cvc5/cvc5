/*********************                                                        */
/*! \file sequences_stats.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for the theory of strings/sequences
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__SEQUENCES_STATS_H
#define CVC4__THEORY__STRINGS__SEQUENCES_STATS_H

#include "expr/kind.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/rewrites.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Statistics for the theory of strings.
 *
 * This is roughly broken up into the following parts:
 * (1) Inferences,
 * (2) Conflicts,
 * (3) Lemmas.
 *
 * "Inferences" (1) are steps invoked during solving, which either trigger:
 * (a) An internal update to the state of the solver (e.g. adding an inferred
 * equality to the equality engine),
 * (b) A call to OutputChannel::conflict,
 * (c) A call to OutputChannel::lemma.
 * For details, see InferenceManager. We track stats on each kind of
 * inference that have been indicated by the solvers in TheoryStrings.
 * Some kinds of inferences are further distinguished by the Kind of the node
 * they operate on (see d_cdSimplifications, d_reductions, d_regexpUnfoldings).
 *
 * "Conflicts" (2) arise from various kinds of reasoning, listed below,
 * where inferences are one of the possible methods for deriving conflicts.
 *
 * "Lemmas" (3) also arise from various kinds of reasoning, listed below,
 * where inferences are one of the possible methods for deriving lemmas.
 */
class SequencesStatistics
{
 public:
  SequencesStatistics();
  ~SequencesStatistics();
  /** Number of calls to run a check where strategy is present */
  IntStat d_checkRuns;
  /** Number of calls to run the strategy */
  IntStat d_strategyRuns;
  //--------------- inferences
  /** Counts the number of applications of each type of inference */
  HistogramStat<Inference> d_inferences;
  /**
   * Counts the number of applications of each type of context-dependent
   * simplification. The sum of this map is equal to the number of EXTF or
   * EXTF_N inferences.
   */
  HistogramStat<Kind> d_cdSimplifications;
  /**
   * Counts the number of applications of each type of reduction. The sum of
   * this map is equal to the number of REDUCTION inferences (when
   * options::stringLazyPreproc is true).
   */
  HistogramStat<Kind> d_reductions;
  /**
   * Counts the number of applications of each type of regular expression
   * positive (resp. negative) unfoldings. The sum of this map is equal to the
   * number of RE_UNFOLD_POS (resp. RE_UNFOLD_NEG) inferences.
   */
  HistogramStat<Kind> d_regexpUnfoldingsPos;
  HistogramStat<Kind> d_regexpUnfoldingsNeg;
  //--------------- end of inferences
  /** Counts the number of applications of each type of rewrite rule */
  HistogramStat<Rewrite> d_rewrites;
  //--------------- conflicts, partition of calls to OutputChannel::conflict
  /** Number of equality engine conflicts */
  IntStat d_conflictsEqEngine;
  /** Number of eager prefix conflicts */
  IntStat d_conflictsEagerPrefix;
  /** Number of inference conflicts */
  IntStat d_conflictsInfer;
  //--------------- end of conflicts
  //--------------- lemmas, partition of calls to OutputChannel::lemma
  /** Number of lemmas added due to eager preprocessing */
  IntStat d_lemmasEagerPreproc;
  /** Number of collect model info splits */
  IntStat d_lemmasCmiSplit;
  /** Number of lemmas added due to registering terms */
  IntStat d_lemmasRegisterTerm;
  /** Number of lemmas added due to registering atomic terms */
  IntStat d_lemmasRegisterTermAtomic;
  /** Number of lemmas added due to inferences */
  IntStat d_lemmasInfer;
  //--------------- end of lemmas
};

}
}
}

#endif /* CVC4__THEORY__STRINGS__SEQUENCES_STATS_H */
