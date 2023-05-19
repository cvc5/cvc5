/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This is an implementation of the Simplex Module for the Simplex for
 * DPLL(T)decision procedure.
 */
#include "theory/arith/linear/fc_simplex.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/error_set.h"
#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

FCSimplexDecisionProcedure::FCSimplexDecisionProcedure(
    Env& env,
    LinearEqualityModule& linEq,
    ErrorSet& errors,
    RaiseConflict conflictChannel,
    TempVarMalloc tvmalloc)
    : SimplexDecisionProcedure(env, linEq, errors, conflictChannel, tvmalloc),
      d_focusSize(0),
      d_focusErrorVar(ARITHVAR_SENTINEL),
      d_focusCoefficients(),
      d_pivotBudget(0),
      d_prevWitnessImprovement(AntiProductive),
      d_witnessImprovementInARow(0),
      d_sgnDisagreements(),
      d_statistics(statisticsRegistry(), "theory::arith::FC::", d_pivots)
{ }

FCSimplexDecisionProcedure::Statistics::Statistics(StatisticsRegistry& sr,
                                                   const std::string& name,
                                                   uint32_t& pivots)
    : d_initialSignalsTime(sr.registerTimer(name + "initialProcessTime")),
      d_initialConflicts(sr.registerInt(name + "UpdateConflicts")),
      d_fcFoundUnsat(sr.registerInt(name + "FoundUnsat")),
      d_fcFoundSat(sr.registerInt(name + "FoundSat")),
      d_fcMissed(sr.registerInt(name + "Missed")),
      d_fcTimer(sr.registerTimer(name + "Timer")),
      d_fcFocusConstructionTimer(sr.registerTimer(name + "Construction")),
      d_selectUpdateForDualLike(
          sr.registerTimer(name + "selectUpdateForDualLike")),
      d_selectUpdateForPrimal(sr.registerTimer(name + "selectUpdateForPrimal")),
      d_finalCheckPivotCounter(
          sr.registerReference<uint32_t>(name + "lastPivots", pivots))
{
}

Result::Status FCSimplexDecisionProcedure::findModel(bool exactResult)
{
  Assert(d_conflictVariables.empty());
  Assert(d_sgnDisagreements.empty());

  d_pivots = 0;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Trace("arith::findModel") << "fcFindModel() trivial" << endl;
    Assert(d_conflictVariables.empty());
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();

  // We must start tracking NOW
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::SUM_METRIC);

  if(initialProcessSignals()){
    d_conflictVariables.purge();
    Trace("arith::findModel") << "fcFindModel() early conflict" << endl;
    Assert(d_conflictVariables.empty());
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Trace("arith::findModel") << "fcFindModel() fixed itself" << endl;
    Assert(d_conflictVariables.empty());
    return Result::SAT;
  }

  Trace("arith::findModel") << "fcFindModel() start non-trivial" << endl;

  exactResult |= d_varOrderPivotLimit < 0;

  d_prevWitnessImprovement = HeuristicDegenerate;
  d_witnessImprovementInARow = 0;

  Result::Status result = Result::UNKNOWN;

  if (result == Result::UNKNOWN)
  {
    if(exactResult){
      d_pivotBudget = -1;
    }else{
      d_pivotBudget = d_varOrderPivotLimit;
    }

    result = dualLike();

    if(result ==  Result::UNSAT){
      ++(d_statistics.d_fcFoundUnsat);
    }else if(d_errorSet.errorEmpty()){
      ++(d_statistics.d_fcFoundSat);
    }else{
      ++(d_statistics.d_fcMissed);
    }
  }

  Assert(!d_errorSet.moreSignals());
  if (result == Result::UNKNOWN && d_errorSet.errorEmpty())
  {
    result = Result::SAT;
  }

  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Trace("arith::findModel") << "end findModel() " << result << endl;

  Assert(d_conflictVariables.empty());
  return result;
}


void FCSimplexDecisionProcedure::logPivot(WitnessImprovement w){
  if(d_pivotBudget > 0) {
    --d_pivotBudget;
  }
  Assert(w != AntiProductive);

  if(w == d_prevWitnessImprovement){
    ++d_witnessImprovementInARow;
    // ignore overflow : probably never reached
    if(d_witnessImprovementInARow == 0){
      --d_witnessImprovementInARow;
    }
  }else{
    if(w != BlandsDegenerate){
      d_witnessImprovementInARow = 1;
    }
    // if w == BlandsDegenerate do not reset the counter
    d_prevWitnessImprovement = w;
  }
  if(strongImprovement(w)){
    d_leavingCountSinceImprovement.purge();
  }

  Trace("logPivot") << "logPivot " << d_prevWitnessImprovement << " "  << d_witnessImprovementInARow << endl;

}

uint32_t FCSimplexDecisionProcedure::degeneratePivotsInARow() const {
  switch(d_prevWitnessImprovement){
  case ConflictFound:
  case ErrorDropped:
  case FocusImproved:
    return 0;
  case HeuristicDegenerate:
  case BlandsDegenerate:
    return d_witnessImprovementInARow;
  // Degenerate is unreachable for its own reasons
  case Degenerate:
  case FocusShrank:
  case AntiProductive:
    Unreachable();
    return -1;
  }
  Unreachable();
}

void FCSimplexDecisionProcedure::adjustFocusAndError(const UpdateInfo& up, const AVIntPairVec& focusChanges){
  uint32_t newErrorSize = d_errorSet.errorSize();
  uint32_t newFocusSize = d_errorSet.focusSize();

  //Assert(!d_conflictVariables.empty() || newFocusSize <= d_focusSize);
  Assert(!d_conflictVariables.empty() || newErrorSize <= d_errorSize);

  if(newFocusSize == 0 || !d_conflictVariables.empty() ){
    tearDownInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer, d_focusErrorVar);
    d_focusErrorVar = ARITHVAR_SENTINEL;
  }else if(2*newFocusSize < d_focusSize ){
    tearDownInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer, d_focusErrorVar);
    d_focusErrorVar = constructInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer);
  }else{
    adjustInfeasFunc(d_statistics.d_fcFocusConstructionTimer, d_focusErrorVar, focusChanges);
  }

  d_errorSize = newErrorSize;
  d_focusSize = newFocusSize;
}

WitnessImprovement FCSimplexDecisionProcedure::adjustFocusShrank(const ArithVarVec& dropped){
  Assert(dropped.size() > 0);
  Assert(d_errorSet.focusSize() == d_focusSize);
  Assert(d_errorSet.focusSize() > dropped.size());

  uint32_t newFocusSize = d_focusSize - dropped.size();
  Assert(newFocusSize > 0);

  if(2 * newFocusSize <= d_focusSize){
    d_errorSet.dropFromFocusAll(dropped);
    tearDownInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer, d_focusErrorVar);
    d_focusErrorVar = constructInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer);
  }else{
    shrinkInfeasFunc(d_statistics.d_fcFocusConstructionTimer, d_focusErrorVar, dropped);
    d_errorSet.dropFromFocusAll(dropped);
  }

  d_focusSize = newFocusSize;
  Assert(d_errorSet.focusSize() == d_focusSize);
  return FocusShrank;
}

WitnessImprovement FCSimplexDecisionProcedure::focusDownToJust(ArithVar v){
  // uint32_t newErrorSize = d_errorSet.errorSize();
  // uint32_t newFocusSize = d_errorSet.focusSize();
  Assert(d_focusSize == d_errorSet.focusSize());
  Assert(d_focusSize > 1);
  Assert(d_errorSet.inFocus(v));

  d_errorSet.focusDownToJust(v);
  Assert(d_errorSet.focusSize() == 1);
  d_focusSize = 1;

  tearDownInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer, d_focusErrorVar);
  d_focusErrorVar = constructInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer);

  return FocusShrank;
}



UpdateInfo FCSimplexDecisionProcedure::selectPrimalUpdate(ArithVar basic, LinearEqualityModule::UpdatePreferenceFunction upf, LinearEqualityModule::VarPreferenceFunction bpf) {
  UpdateInfo selected;

  Trace("arith::selectPrimalUpdate")
      << "selectPrimalUpdate" << endl
      << basic << " " << d_tableau.basicRowLength(basic) << " "
      << d_linEq.debugBasicAtBoundCount(basic) << endl;

  static constexpr int s_maxCandidatesAfterImprove = 3;
  bool isFocus = basic == d_focusErrorVar;
  Assert(isFocus || d_errorSet.inError(basic));
  int basicDir =  isFocus? 1 : d_errorSet.getSgn(basic);
  bool dualLike = !isFocus && d_focusSize > 1;

  if(!isFocus){
    loadFocusSigns();
  }

  decreasePenalties();

  typedef std::vector<Cand> CandVector;
  CandVector candidates;

  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(basic); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    if(curr == basic){ continue; }

    int sgn = e.getCoefficient().sgn();
    int curr_movement = basicDir * sgn;

    bool candidate =
      (curr_movement > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
      (curr_movement < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0);

    Trace("arith::selectPrimalUpdate")
      << "storing " << basic
      << " " << curr
      << " " << candidate
      << " " << e.getCoefficient()
      << " " << curr_movement
      << " " << focusCoefficient(curr) << endl;

    if(!candidate) { continue; }

    if(!isFocus){
      const Rational& focusC = focusCoefficient(curr);
      Assert(dualLike || !focusC.isZero());
      if(dualLike && curr_movement != focusC.sgn()){
        Trace("arith::selectPrimalUpdate") << "sgn disagreement " << curr << endl;
        d_sgnDisagreements.push_back(curr);
        continue;
      }else{
        candidates.push_back(Cand(curr, penalty(curr), curr_movement, &focusC));
      }
    }else{
      candidates.push_back(Cand(curr, penalty(curr), curr_movement, &e.getCoefficient()));
    }
  }

  CompPenaltyColLength colCmp(&d_linEq, options().arith.havePenalties);
  CandVector::iterator i = candidates.begin();
  CandVector::iterator end = candidates.end();
  std::make_heap(i, end, colCmp);

  bool checkEverything = d_pivots == 0;

  int candidatesAfterFocusImprove = 0;
  while(i != end && (checkEverything || candidatesAfterFocusImprove <= s_maxCandidatesAfterImprove)){
    std::pop_heap(i, end, colCmp);
    --end;
    Cand& cand = (*end);
    ArithVar curr = cand.d_nb;
    const Rational& coeff = *cand.d_coeff;

    LinearEqualityModule::UpdatePreferenceFunction leavingPrefFunc = selectLeavingFunction(curr);
    UpdateInfo currProposal = d_linEq.speculativeUpdate(curr, coeff, leavingPrefFunc);

    Trace("arith::selectPrimalUpdate")
      << "selected " << selected << endl
      << "currProp " << currProposal << endl
      << "coeff " << coeff << endl;

    Assert(!currProposal.uninitialized());

    if(candidatesAfterFocusImprove > 0){
      candidatesAfterFocusImprove++;
    }

    if(selected.uninitialized() || (d_linEq.*upf)(selected, currProposal)){

      selected = currProposal;
      WitnessImprovement w = selected.getWitness(false);
      Trace("arith::selectPrimalUpdate") << "selected " << w << endl;
      setPenalty(curr, w);
      if(improvement(w)){
        bool exitEarly;
        switch(w){
        case ConflictFound: exitEarly = true; break;
        case ErrorDropped:
          if(checkEverything){
            exitEarly = d_errorSize + selected.errorsChange() == 0;
            Trace("arith::selectPrimalUpdate")
              << "ee " << d_errorSize << " "
              << selected.errorsChange() << " "
              << d_errorSize + selected.errorsChange() << endl;
          }else{
            exitEarly = true;
          }
          break;
        case FocusImproved:
          candidatesAfterFocusImprove = 1;
          exitEarly = false;
          break;
        default:
          exitEarly = false; break;
        }
        if(exitEarly){ break; }
      }
    }else{
      Trace("arith::selectPrimalUpdate") << "dropped "<< endl;
    }

  }

  if(!isFocus){
    unloadFocusSigns();
  }
  return selected;
}

bool FCSimplexDecisionProcedure::debugCheckWitness(const UpdateInfo& inf, WitnessImprovement w, bool useBlands){
  if(inf.getWitness(useBlands) == w){
    switch(w){
    case ConflictFound: return inf.foundConflict();
    case ErrorDropped: return inf.errorsChange() < 0;
    case FocusImproved: return inf.focusDirection() > 0;
    case FocusShrank: return false; // This is not a valid output
    case Degenerate: return false; // This is not a valid output
    case BlandsDegenerate: return useBlands;
    case HeuristicDegenerate: return !useBlands;
    case AntiProductive: return false;
    }
  }
  return false;
}

WitnessImprovement FCSimplexDecisionProcedure::primalImproveError(ArithVar errorVar){
  bool useBlands = degeneratePivotsInARow() >= s_maxDegeneratePivotsBeforeBlandsOnLeaving;
  UpdateInfo selected = selectUpdateForPrimal (errorVar, useBlands);
  Assert(!selected.uninitialized());
  WitnessImprovement w = selected.getWitness(useBlands);
  Assert(debugCheckWitness(selected, w, useBlands));

  updateAndSignal(selected, w);
  logPivot(w);
  return w;
}


WitnessImprovement FCSimplexDecisionProcedure::focusUsingSignDisagreements(ArithVar basic){
  Assert(!d_sgnDisagreements.empty());
  Assert(d_errorSet.focusSize() >= 2);

  if(TraceIsOn("arith::focus")){
    d_errorSet.debugPrint(Trace("arith::focus"));
  }

  ArithVar nb = d_linEq.minBy(d_sgnDisagreements, &LinearEqualityModule::minColLength);
  const Tableau::Entry& e_evar_nb = d_tableau.basicFindEntry(basic, nb);
  int oppositeSgn = - (e_evar_nb.getCoefficient().sgn());
  Trace("arith::focus") << "focusUsingSignDisagreements " << basic << " " << oppositeSgn << endl;

  ArithVarVec dropped;

  Tableau::ColIterator colIter = d_tableau.colIterator(nb);
  for(; !colIter.atEnd(); ++colIter){
    const Tableau::Entry& entry = *colIter;
    Assert(entry.getColVar() == nb);

    int sgn = entry.getCoefficient().sgn();
    Trace("arith::focus")
      << "on row "
      << d_tableau.rowIndexToBasic(entry.getRowIndex())
      << " "
      << entry.getCoefficient() << endl;
    ArithVar currRow = d_tableau.rowIndexToBasic(entry.getRowIndex());
    if(d_errorSet.inError(currRow) && d_errorSet.inFocus(currRow)){
      int errSgn = d_errorSet.getSgn(currRow);

      if(errSgn * sgn == oppositeSgn){
        dropped.push_back(currRow);
        Trace("arith::focus") << "dropping from focus " << currRow << endl;
      }
    }
  }

  d_sgnDisagreements.clear();
  return adjustFocusShrank(dropped);
}

bool debugSelectedErrorDropped(const UpdateInfo& selected, int32_t prevErrorSize, int32_t currErrorSize){
  int diff = currErrorSize - prevErrorSize;
  return selected.foundConflict() || diff == selected.errorsChange();
}

void FCSimplexDecisionProcedure::debugPrintSignal(ArithVar updated) const{
  Trace("updateAndSignal") << "updated basic " << updated;
  Trace("updateAndSignal") << " length " << d_tableau.basicRowLength(updated);
  Trace("updateAndSignal") << " consistent " << d_variables.assignmentIsConsistent(updated);
  int dir = !d_variables.assignmentIsConsistent(updated) ?
    d_errorSet.getSgn(updated) : 0;
  Trace("updateAndSignal") << " dir " << dir;
  Trace("updateAndSignal") << " debugBasicAtBoundCount " << d_linEq.debugBasicAtBoundCount(updated) << endl;
}

bool debugUpdatedBasic(const UpdateInfo& selected, ArithVar updated){
  if(selected.describesPivot() &&  updated == selected.leaving()){
    return selected.foundConflict();
  }else{
    return true;
  }
}

void FCSimplexDecisionProcedure::updateAndSignal(const UpdateInfo& selected, WitnessImprovement w){
  ArithVar nonbasic = selected.nonbasic();

  Trace("updateAndSignal") << "updateAndSignal " << selected << endl;

  stringstream ss;

  if(selected.describesPivot()){
    ConstraintP limiting = selected.limiting();
    ArithVar basic = limiting->getVariable();
    Assert(d_linEq.basicIsTracked(basic));
    d_linEq.pivotAndUpdate(basic, nonbasic, limiting->getValue());
  }else{
    Assert(!selected.unbounded() || selected.errorsChange() < 0);

    DeltaRational newAssignment =
      d_variables.getAssignment(nonbasic) + selected.nonbasicDelta();

    d_linEq.updateTracked(nonbasic, newAssignment);
  }
  d_pivots++;

  increaseLeavingCount(nonbasic);

  vector< pair<ArithVar, int> > focusChanges;
  while(d_errorSet.moreSignals()){
    ArithVar updated = d_errorSet.topSignal();
    int prevFocusSgn = d_errorSet.popSignal();

    if(d_tableau.isBasic(updated)){
      Assert(!d_variables.assignmentIsConsistent(updated)
             == d_errorSet.inError(updated));
      if(TraceIsOn("updateAndSignal")){debugPrintSignal(updated);}
      if(!d_variables.assignmentIsConsistent(updated)){
        if(checkBasicForConflict(updated)){
          reportConflict(updated);
          Assert(debugUpdatedBasic(selected, updated));
        }
      }
    }else{
      Trace("updateAndSignal") << "updated nonbasic " << updated << endl;
    }
    int currFocusSgn = d_errorSet.focusSgn(updated);
    if(currFocusSgn != prevFocusSgn){
      int change = currFocusSgn - prevFocusSgn;
      focusChanges.push_back(make_pair(updated, change));
    }
  }

  if(TraceIsOn("error")){ d_errorSet.debugPrint(Trace("error")); }

  Assert(
      debugSelectedErrorDropped(selected, d_errorSize, d_errorSet.errorSize()));

  adjustFocusAndError(selected, focusChanges);
}

WitnessImprovement FCSimplexDecisionProcedure::dualLikeImproveError(ArithVar errorVar){
  Assert(d_sgnDisagreements.empty());
  Assert(d_focusSize > 1);

  UpdateInfo selected = selectUpdateForDualLike(errorVar);

  if(selected.uninitialized()){
    // we found no proposals
    // If this is empty, there must be an error on this variable!
    // this should not be possible. It Should have been caught as a signal earlier
    WitnessImprovement dropped = focusUsingSignDisagreements(errorVar);
    Assert(d_sgnDisagreements.empty());

    return dropped;
  }else{
    d_sgnDisagreements.clear();
  }

  Assert(d_sgnDisagreements.empty());
  Assert(!selected.uninitialized());

  if(selected.focusDirection() == 0 &&
     d_prevWitnessImprovement == HeuristicDegenerate &&
     d_witnessImprovementInARow >= s_focusThreshold){

    Trace("focusDownToJust") << "focusDownToJust " << errorVar << endl;

    return focusDownToJust(errorVar);
  }else{
    WitnessImprovement w = selected.getWitness(false);
    Assert(debugCheckWitness(selected, w, false));
    updateAndSignal(selected, w);
    logPivot(w);
    return w;
  }
}

WitnessImprovement FCSimplexDecisionProcedure::focusDownToLastHalf(){
  Assert(d_focusSize >= 2);

  Trace("focusDownToLastHalf") << "focusDownToLastHalf "
       << d_errorSet.errorSize()  << " "
       << d_errorSet.focusSize() << " ";

  uint32_t half = d_focusSize/2;
  ArithVarVec buf;
  for(ErrorSet::focus_iterator i = d_errorSet.focusBegin(),
        i_end = d_errorSet.focusEnd(); i != i_end; ++i){
    if(half > 0){
      --half;
    } else{
      buf.push_back(*i);
    }
  }
  WitnessImprovement w = adjustFocusShrank(buf);
  Trace("focusDownToLastHalf") << "-> " << d_errorSet.focusSize() << endl;
  return w;
}

WitnessImprovement FCSimplexDecisionProcedure::selectFocusImproving() {
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  Assert(d_focusSize >= 2);

  LinearEqualityModule::UpdatePreferenceFunction upf =
    &LinearEqualityModule::preferWitness<true>;

  LinearEqualityModule::VarPreferenceFunction bpf =
    &LinearEqualityModule::minRowLength;

  UpdateInfo selected = selectPrimalUpdate(d_focusErrorVar, upf, bpf);

  if(selected.uninitialized()){
    Trace("selectFocusImproving") << "focus is optimum, but we don't have sat/conflict yet" << endl;

    return focusDownToLastHalf();
  }
  Assert(!selected.uninitialized());
  WitnessImprovement w = selected.getWitness(false);
  Assert(debugCheckWitness(selected, w, false));

  if(degenerate(w)){
    Trace("selectFocusImproving") << "only degenerate" << endl;
    if(d_prevWitnessImprovement == HeuristicDegenerate &&
       d_witnessImprovementInARow >= s_focusThreshold){
      Trace("selectFocusImproving") << "focus down been degenerate too long" << endl;
      return focusDownToLastHalf();
    }else{
      Trace("selectFocusImproving") << "taking degenerate" << endl;
    }
  }
  Trace("selectFocusImproving") << "selectFocusImproving did this " << selected << endl;

  updateAndSignal(selected, w);
  logPivot(w);
  return w;
}

bool FCSimplexDecisionProcedure::debugDualLike(WitnessImprovement w,
                                               ostream& out,
                                               uint32_t prevFocusSize,
                                               uint32_t prevErrorSize) const
{
  out << "DLV() ";
  switch(w){
  case ConflictFound:
    out << "found conflict" << endl;
    return !d_conflictVariables.empty();
  case ErrorDropped:
    out << "dropped " << prevErrorSize - d_errorSize << endl;
    return d_errorSize < prevErrorSize;
  case FocusImproved:
    out << "focus improved"<< endl;
    return d_errorSize == prevErrorSize;
  case FocusShrank:
    out << "focus shrank"<< endl;
    return d_errorSize == prevErrorSize && prevFocusSize > d_focusSize;
  case BlandsDegenerate:
    out << "bland degenerate"<< endl;
    return true;
  case HeuristicDegenerate:
    out << "heuristic degenerate"<< endl;
    return true;
  case AntiProductive:
    out << "focus blur" << endl;
    return prevFocusSize == 0;
  case Degenerate:
    return false;
  }
  return false;
}

Result::Status FCSimplexDecisionProcedure::dualLike()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_fcTimer);

  Assert(d_sgnDisagreements.empty());
  Assert(d_pivotBudget != 0);
  Assert(d_errorSize == d_errorSet.errorSize());
  Assert(d_errorSize > 0);
  Assert(d_focusSize == d_errorSet.focusSize());
  Assert(d_focusSize > 0);
  Assert(d_conflictVariables.empty());
  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);

  d_scores.purge();
  d_focusErrorVar = constructInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer);


  while(d_pivotBudget != 0  && d_errorSize > 0 && d_conflictVariables.empty()){
    Trace("dualLike") << "dualLike " << endl;

    Assert(d_errorSet.noSignals());

    WitnessImprovement w = AntiProductive;
    uint32_t prevFocusSize = d_focusSize;
    uint32_t prevErrorSize = d_errorSize;

    if(d_focusSize == 0){
      Assert(d_errorSize == d_errorSet.errorSize());
      Assert(d_focusErrorVar == ARITHVAR_SENTINEL);

      d_errorSet.blur();

      d_focusSize = d_errorSet.focusSize();

      Assert(d_errorSize == d_focusSize);
      Assert(d_errorSize >= 1);

      d_focusErrorVar = constructInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer);

      Trace("dualLike") << "blur " << d_focusSize << endl;
    }else if(d_focusSize == 1){
      // Possible outcomes:
      // - errorSet size shrunk
      // -- fixed v
      // -- fixed something other than v
      // - conflict
      // - budget was exhausted

      ArithVar e = d_errorSet.topFocusVariable();
      Trace("dualLike") << "primalImproveError " << e << endl;
      w = primalImproveError(e);
    }else{

      // Possible outcomes:
      // - errorSet size shrunk
      // -- fixed v
      // -- fixed something other than v
      // - conflict
      // - budget was exhausted
      // - focus went down
      Assert(d_focusSize > 1);
      ArithVar e = d_errorSet.topFocusVariable();
      static constexpr unsigned s_sumMetricThreshold = 1;
      if(d_errorSet.sumMetric(e) <= s_sumMetricThreshold){
        Trace("dualLike") << "dualLikeImproveError " << e << endl;
        w = dualLikeImproveError(e);
      }else{
        Trace("dualLike") << "selectFocusImproving " << endl;
        w = selectFocusImproving();
      }
    }
    Trace("dualLike") << "witnessImprovement: " << w << endl;
    Assert(d_focusSize == d_errorSet.focusSize());
    Assert(d_errorSize == d_errorSet.errorSize());

    Assert(debugDualLike(w, Trace("dualLike"), prevFocusSize, prevErrorSize));
    Trace("dualLike") << "Focus size " << d_focusSize << " (was " << prevFocusSize << ")" << endl;
    Trace("dualLike") << "Error size " << d_errorSize << " (was " << prevErrorSize << ")" << endl;
  }


  if(d_focusErrorVar != ARITHVAR_SENTINEL){
    tearDownInfeasiblityFunction(d_statistics.d_fcFocusConstructionTimer, d_focusErrorVar);
    d_focusErrorVar = ARITHVAR_SENTINEL;
  }

  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
  if(!d_conflictVariables.empty()){
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Assert(d_errorSet.noSignals());
    return Result::SAT;
  }else{
    Assert(d_pivotBudget == 0);
    return Result::UNKNOWN;
  }
}


void FCSimplexDecisionProcedure::loadFocusSigns(){
  Assert(d_focusCoefficients.empty());
  Assert(d_focusErrorVar != ARITHVAR_SENTINEL);
  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(d_focusErrorVar); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    d_focusCoefficients.set(curr, &e.getCoefficient());
  }
}

void FCSimplexDecisionProcedure::unloadFocusSigns(){
  d_focusCoefficients.purge();
}

const Rational& FCSimplexDecisionProcedure::focusCoefficient(ArithVar nb) const {
  if(d_focusCoefficients.isKey(nb)){
    return *(d_focusCoefficients[nb]);
  }else{
    return d_zero;
  }
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
