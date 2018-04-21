/*********************                                                        */
/*! \file attempt_solution_simplex.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Paul Meng, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is an implementation of the Simplex Module for the Simplex for DPLL(T)
 ** decision procedure.
 **
 ** This implements the Simplex module for the Simpelx for DPLL(T) decision procedure.
 ** See the Simplex for DPLL(T) technical report for more background.(citation?)
 ** This shares with the theory a Tableau, and a PartialModel that:
 **  - satisfies the equalities in the Tableau, and
 **  - the assignment for the non-basic variables satisfies their bounds.
 ** This is required to either produce a conflict or satisifying PartialModel.
 ** Further, we require being told when a basic variable updates its value.
 **
 ** During the Simplex search we maintain a queue of variables.
 ** The queue is required to contain all of the basic variables that voilate their bounds.
 ** As elimination from the queue is more efficient to be done lazily,
 ** we do not maintain that the queue of variables needs to be only basic variables or only
 ** variables that satisfy their bounds.
 **
 ** The simplex procedure roughly follows Alberto's thesis. (citation?)
 ** There is one round of selecting using a heuristic pivoting rule. (See PreferenceFunction
 ** Documentation for the available options.)
 ** The non-basic variable is the one that appears in the fewest pivots. (Bruno says that
 ** Leonardo invented this first.)
 ** After this, Bland's pivot rule is invoked.
 **
 ** During this proccess, we periodically inspect the queue of variables to
 ** 1) remove now extraneous extries,
 ** 2) detect conflicts that are "waiting" on the queue but may not be detected by the
 **  current queue heuristics, and
 ** 3) detect multiple conflicts.
 **
 ** Conflicts are greedily slackened to use the weakest bounds that still produce the
 ** conflict.
 **
 ** Extra things tracked atm: (Subject to change at Tim's whims)
 ** - A superset of all of the newly pivoted variables.
 ** - A queue of additional conflicts that were discovered by Simplex.
 **   These are theory valid and are currently turned into lemmas
 **/


#include "cvc4_private.h"

#pragma once

#include "theory/arith/simplex.h"
#include "theory/arith/approx_simplex.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {

class AttemptSolutionSDP : public SimplexDecisionProcedure {
public:
  AttemptSolutionSDP(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  Result::Sat attempt(const ApproximateSimplex::Solution& sol);

  Result::Sat findModel(bool exactResult) override { Unreachable(); }

 private:
  bool matchesNewValue(const DenseMap<DeltaRational>& nv, ArithVar v) const;

  bool processSignals(){
    TimerStat &timer = d_statistics.d_queueTime;
    IntStat& conflictStat  = d_statistics.d_conflicts;
    return standardProcessSignals(timer, conflictStat);
  }
  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    TimerStat d_searchTime;
    TimerStat d_queueTime;
    IntStat d_conflicts;

    Statistics();
    ~Statistics();
  } d_statistics;
};/* class AttemptSolutionSDP */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
