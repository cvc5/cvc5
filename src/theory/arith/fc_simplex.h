/*********************                                                        */
/*! \file fc_simplex.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

class FCSimplexDecisionProcedure : public SimplexDecisionProcedure{
public:
  FCSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);

  Result::Sat findModel(bool exactResult) override;

  // other error variables are dropping
  WitnessImprovement dualLikeImproveError(ArithVar evar);
  WitnessImprovement primalImproveError(ArithVar evar);

  // dual like
  // - found conflict
  // - satisfied error set
  Result::Sat dualLike();

private:
  static const uint32_t PENALTY = 4;
  DenseMultiset d_scores;
  void decreasePenalties(){ d_scores.removeOneOfEverything(); }
  uint32_t penalty(ArithVar x) const { return d_scores.count(x); }
  void setPenalty(ArithVar x, WitnessImprovement w){
    if(improvement(w)){
      if(d_scores.count(x) > 0){
        d_scores.removeAll(x);
      }
    }else{
      d_scores.setCount(x, PENALTY);
    }
  }

  /** The size of the focus set. */
  uint32_t d_focusSize;

  /** The current error focus variable. */
  ArithVar d_focusErrorVar;

  /**
   * The signs of the coefficients in the focus set.
   * This is empty until this has been loaded.
   */
  DenseMap<const Rational*> d_focusCoefficients;

  /**
   * Loads the signs of the coefficients of the variables on the row d_focusErrorVar
   * into d_focusSgns.
   */
  void loadFocusSigns();

  /** Unloads the information from d_focusSgns. */
  void unloadFocusSigns();

  /**
   * The signs of a variable in the row of d_focusErrorVar.
   * d_focusSgns must be loaded.
   */
  const Rational& focusCoefficient(ArithVar nb) const;

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

  bool debugDualLike(WitnessImprovement w, std::ostream& out,
                     int instance,
                     uint32_t prevFocusSize, uint32_t prevErrorSize) const;

  void debugPrintSignal(ArithVar updated) const;

  ArithVarVec d_sgnDisagreements;

  //static PivotImprovement pivotImprovement(const UpdateInfo& selected, bool useBlands = false);

  void logPivot(WitnessImprovement w);

  void updateAndSignal(const UpdateInfo& selected, WitnessImprovement w);

  UpdateInfo selectPrimalUpdate(ArithVar error,
                                LinearEqualityModule::UpdatePreferenceFunction upf,
                                LinearEqualityModule::VarPreferenceFunction bpf);


  UpdateInfo selectUpdateForDualLike(ArithVar basic){
    TimerStat::CodeTimer codeTimer(d_statistics.d_selectUpdateForDualLike);

    LinearEqualityModule::UpdatePreferenceFunction upf =
      &LinearEqualityModule::preferWitness<true>;
    LinearEqualityModule::VarPreferenceFunction bpf =
      &LinearEqualityModule::minVarOrder;
    return selectPrimalUpdate(basic, upf, bpf);
  }

  UpdateInfo selectUpdateForPrimal(ArithVar basic, bool useBlands){
    TimerStat::CodeTimer codeTimer(d_statistics.d_selectUpdateForPrimal);

    LinearEqualityModule::UpdatePreferenceFunction upf;
    if(useBlands) {
      upf = &LinearEqualityModule::preferWitness<false>;
    } else {
      upf = &LinearEqualityModule::preferWitness<true>;
    }

    LinearEqualityModule::VarPreferenceFunction bpf = useBlands ?
      &LinearEqualityModule::minVarOrder :
      &LinearEqualityModule::minRowLength;

    return selectPrimalUpdate(basic, upf, bpf);
  }
  WitnessImprovement selectFocusImproving() ;

  WitnessImprovement focusUsingSignDisagreements(ArithVar basic);
  WitnessImprovement focusDownToLastHalf();
  WitnessImprovement adjustFocusShrank(const ArithVarVec& drop);
  WitnessImprovement focusDownToJust(ArithVar v);


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
    bool res = standardProcessSignals(timer, conflictStat);
    d_focusSize = d_errorSet.focusSize();
    return res;
  }

  static bool debugCheckWitness(const UpdateInfo& inf, WitnessImprovement w, bool useBlands);

  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    TimerStat d_initialSignalsTime;
    IntStat d_initialConflicts;

    IntStat d_fcFoundUnsat;
    IntStat d_fcFoundSat;
    IntStat d_fcMissed;

    TimerStat d_fcTimer;
    TimerStat d_fcFocusConstructionTimer;

    TimerStat d_selectUpdateForDualLike;
    TimerStat d_selectUpdateForPrimal;

    ReferenceStat<uint32_t> d_finalCheckPivotCounter;

    Statistics(uint32_t& pivots);
    ~Statistics();
  } d_statistics;
};/* class FCSimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
