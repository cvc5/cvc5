/*********************                                                        */
/*! \file soi_simplex.h
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

#include <stdint.h>

#include "theory/arith/simplex.h"
#include "util/dense_map.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {

class SumOfInfeasibilitiesSPD : public SimplexDecisionProcedure {
public:
  SumOfInfeasibilitiesSPD(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  Result::Sat findModel(bool exactResult) override;

  // other error variables are dropping
  WitnessImprovement dualLikeImproveError(ArithVar evar);
  WitnessImprovement primalImproveError(ArithVar evar);

private:
  /** The current sum of infeasibilities variable. */
  ArithVar d_soiVar;

  // dual like
  // - found conflict
  // - satisfied error set
  Result::Sat sumOfInfeasibilities();

  // static const uint32_t PENALTY = 4;
  // DenseMultiset d_scores;
  // void decreasePenalties(){ d_scores.removeOneOfEverything(); }
  // uint32_t penalty(ArithVar x) const { return d_scores.count(x); }
  // void setPenalty(ArithVar x, WitnessImprovement w){
  //   if(improvement(w)){
  //     if(d_scores.count(x) > 0){
  //       d_scores.removeAll(x);
  //     }
  //   }else{
  //     d_scores.setCount(x, PENALTY);
  //   }
  // }

  int32_t d_pivotBudget;
  // enum PivotImprovement {
  //   ErrorDropped,
  //   NonDegenerate,
  //   HeuristicDegenerate,
  //   BlandsDegenerate
  // };

  WitnessImprovement d_prevWitnessImprovement;
  uint32_t d_witnessImprovementInARow;

  uint32_t degeneratePivotsInARow() const;

  static const uint32_t s_focusThreshold = 6;
  static const uint32_t s_maxDegeneratePivotsBeforeBlandsOnLeaving = 100;
  static const uint32_t s_maxDegeneratePivotsBeforeBlandsOnEntering = 10;

  DenseMap<uint32_t> d_leavingCountSinceImprovement;
  void increaseLeavingCount(ArithVar x){
    if(!d_leavingCountSinceImprovement.isKey(x)){
      d_leavingCountSinceImprovement.set(x,1);
    }else{
      (d_leavingCountSinceImprovement.get(x))++;
    }
  }
  LinearEqualityModule::UpdatePreferenceFunction selectLeavingFunction(ArithVar x){
    bool useBlands = d_leavingCountSinceImprovement.isKey(x) &&
      d_leavingCountSinceImprovement[x] >= s_maxDegeneratePivotsBeforeBlandsOnEntering;
    if(useBlands) {
      return &LinearEqualityModule::preferWitness<false>;
    } else {
      return &LinearEqualityModule::preferWitness<true>;
    }
  }

  bool debugSOI(WitnessImprovement w, std::ostream& out, int instance) const;

  void debugPrintSignal(ArithVar updated) const;

  ArithVarVec d_sgnDisagreements;

  void logPivot(WitnessImprovement w);

  void updateAndSignal(const UpdateInfo& selected, WitnessImprovement w);

  UpdateInfo selectUpdate(LinearEqualityModule::UpdatePreferenceFunction upf,
                          LinearEqualityModule::VarPreferenceFunction bpf);


  // UpdateInfo selectUpdateForDualLike(ArithVar basic){
  //   TimerStat::CodeTimer codeTimer(d_statistics.d_selectUpdateForDualLike);

  //   LinearEqualityModule::UpdatePreferenceFunction upf =
  //     &LinearEqualityModule::preferWitness<true>;
  //   LinearEqualityModule::VarPreferenceFunction bpf =
  //     &LinearEqualityModule::minVarOrder;
  //   return selectPrimalUpdate(basic, upf, bpf);
  // }

  // UpdateInfo selectUpdateForPrimal(ArithVar basic, bool useBlands){
  //   TimerStat::CodeTimer codeTimer(d_statistics.d_selectUpdateForPrimal);

  //   LinearEqualityModule::UpdatePreferenceFunction upf = useBlands ?
  //     &LinearEqualityModule::preferWitness<false>:
  //     &LinearEqualityModule::preferWitness<true>;

  //   LinearEqualityModule::VarPreferenceFunction bpf = useBlands ?
  //     &LinearEqualityModule::minVarOrder :
  //     &LinearEqualityModule::minRowLength;
  //   bpf = &LinearEqualityModule::minVarOrder;

  //   return selectPrimalUpdate(basic, upf, bpf);
  // }
  // WitnessImprovement selectFocusImproving() ;
  WitnessImprovement soiRound();
  WitnessImprovement SOIConflict();
  std::vector< ArithVarVec > greedyConflictSubsets();
  bool generateSOIConflict(const ArithVarVec& subset);

  // WitnessImprovement focusUsingSignDisagreements(ArithVar basic);
  // WitnessImprovement focusDownToLastHalf();
  // WitnessImprovement adjustFocusShrank(const ArithVarVec& drop);
  // WitnessImprovement focusDownToJust(ArithVar v);


  void adjustFocusAndError(const UpdateInfo& up, const AVIntPairVec& focusChanges);

  /**
   * This is the main simplex for DPLL(T) loop.
   * It runs for at most maxIterations.
   *
   * Returns true iff it has found a conflict.
   * d_conflictVariable will be set and the conflict for this row is reported.
   */
  bool searchForFeasibleSolution(uint32_t maxIterations);

  bool initialProcessSignals(){
    TimerStat &timer = d_statistics.d_initialSignalsTime;
    IntStat& conflictStat  = d_statistics.d_initialConflicts;
    return standardProcessSignals(timer, conflictStat);
  }

  void quickExplain();
  DenseSet d_qeInSoi;
  DenseSet d_qeInUAndNotInSoi;
  ArithVarVec d_qeConflict;
  ArithVarVec d_qeGreedyOrder;
  sgn_table d_qeSgns;

  uint32_t quickExplainRec(uint32_t cEnd, uint32_t uEnd);
  void qeAddRange(uint32_t begin, uint32_t end);
  void qeRemoveRange(uint32_t begin, uint32_t end);
  void qeSwapRange(uint32_t N, uint32_t r, uint32_t s);

  unsigned trySet(const ArithVarVec& set);
  unsigned tryAllSubsets(const ArithVarVec& set, unsigned depth, ArithVarVec& tmp);

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    TimerStat d_initialSignalsTime;
    IntStat d_initialConflicts;

    IntStat d_soiFoundUnsat;
    IntStat d_soiFoundSat;
    IntStat d_soiMissed;

    IntStat d_soiConflicts;
    IntStat d_hasToBeMinimal;
    IntStat d_maybeNotMinimal;

    TimerStat d_soiTimer;
    TimerStat d_soiFocusConstructionTimer;
    TimerStat d_soiConflictMinimization;
    TimerStat d_selectUpdateForSOI;

    ReferenceStat<uint32_t> d_finalCheckPivotCounter;

    Statistics(uint32_t& pivots);
    ~Statistics();
  } d_statistics;
};/* class FCSimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
