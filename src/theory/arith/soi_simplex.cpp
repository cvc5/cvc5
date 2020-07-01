/*********************                                                        */
/*! \file soi_simplex.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "theory/arith/soi_simplex.h"

#include <algorithm>

#include "base/output.h"
#include "options/arith_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/constraint.h"
#include "util/statistics_registry.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {


SumOfInfeasibilitiesSPD::SumOfInfeasibilitiesSPD(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
  , d_soiVar(ARITHVAR_SENTINEL)
  , d_pivotBudget(0)
  , d_prevWitnessImprovement(AntiProductive)
  , d_witnessImprovementInARow(0)
  , d_sgnDisagreements()
  , d_statistics(d_pivots)
{ }

SumOfInfeasibilitiesSPD::Statistics::Statistics(uint32_t& pivots):
  d_initialSignalsTime("theory::arith::SOI::initialProcessTime"),
  d_initialConflicts("theory::arith::SOI::UpdateConflicts", 0),
  d_soiFoundUnsat("theory::arith::SOI::FoundUnsat", 0),
  d_soiFoundSat("theory::arith::SOI::FoundSat", 0),
  d_soiMissed("theory::arith::SOI::Missed", 0),
  d_soiConflicts("theory::arith::SOI::ConfMin::num", 0),
  d_hasToBeMinimal("theory::arith::SOI::HasToBeMin", 0),
  d_maybeNotMinimal("theory::arith::SOI::MaybeNotMin", 0),
  d_soiTimer("theory::arith::SOI::Time"),
  d_soiFocusConstructionTimer("theory::arith::SOI::Construction"),
  d_soiConflictMinimization("theory::arith::SOI::Conflict::Minimization"),
  d_selectUpdateForSOI("theory::arith::SOI::selectSOI"),
  d_finalCheckPivotCounter("theory::arith::SOI::lastPivots", pivots)
{
  smtStatisticsRegistry()->registerStat(&d_initialSignalsTime);
  smtStatisticsRegistry()->registerStat(&d_initialConflicts);

  smtStatisticsRegistry()->registerStat(&d_soiFoundUnsat);
  smtStatisticsRegistry()->registerStat(&d_soiFoundSat);
  smtStatisticsRegistry()->registerStat(&d_soiMissed);

  smtStatisticsRegistry()->registerStat(&d_soiConflicts);
  smtStatisticsRegistry()->registerStat(&d_hasToBeMinimal);
  smtStatisticsRegistry()->registerStat(&d_maybeNotMinimal);

  smtStatisticsRegistry()->registerStat(&d_soiTimer);
  smtStatisticsRegistry()->registerStat(&d_soiFocusConstructionTimer);

  smtStatisticsRegistry()->registerStat(&d_soiConflictMinimization);

  smtStatisticsRegistry()->registerStat(&d_selectUpdateForSOI);

  smtStatisticsRegistry()->registerStat(&d_finalCheckPivotCounter);
}

SumOfInfeasibilitiesSPD::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_initialSignalsTime);
  smtStatisticsRegistry()->unregisterStat(&d_initialConflicts);

  smtStatisticsRegistry()->unregisterStat(&d_soiFoundUnsat);
  smtStatisticsRegistry()->unregisterStat(&d_soiFoundSat);
  smtStatisticsRegistry()->unregisterStat(&d_soiMissed);

  smtStatisticsRegistry()->unregisterStat(&d_soiConflicts);
  smtStatisticsRegistry()->unregisterStat(&d_hasToBeMinimal);
  smtStatisticsRegistry()->unregisterStat(&d_maybeNotMinimal);

  smtStatisticsRegistry()->unregisterStat(&d_soiTimer);
  smtStatisticsRegistry()->unregisterStat(&d_soiFocusConstructionTimer);

  smtStatisticsRegistry()->unregisterStat(&d_soiConflictMinimization);

  smtStatisticsRegistry()->unregisterStat(&d_selectUpdateForSOI);
  smtStatisticsRegistry()->unregisterStat(&d_finalCheckPivotCounter);
}

Result::Sat SumOfInfeasibilitiesSPD::findModel(bool exactResult){
  Assert(d_conflictVariables.empty());
  Assert(d_sgnDisagreements.empty());

  d_pivots = 0;
  static thread_local unsigned int instance = 0;
  instance = instance + 1;
  static const bool verbose = false;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Debug("soi::findModel") << "soiFindModel("<< instance <<") trivial" << endl;
    Assert(d_conflictVariables.empty());
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();

  // We must start tracking NOW
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::SUM_METRIC);

  if(initialProcessSignals()){
    d_conflictVariables.purge();
    if(verbose){ Message() << "fcFindModel("<< instance <<") early conflict" << endl; }
    Debug("soi::findModel") << "fcFindModel("<< instance <<") early conflict" << endl;
    Assert(d_conflictVariables.empty());
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Debug("soi::findModel") << "fcFindModel("<< instance <<") fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    Assert(d_conflictVariables.empty());
    return Result::SAT;
  }

  Debug("soi::findModel") << "fcFindModel(" << instance <<") start non-trivial" << endl;

  exactResult |= options::arithStandardCheckVarOrderPivots() < 0;

  d_prevWitnessImprovement = HeuristicDegenerate;
  d_witnessImprovementInARow = 0;

  Result::Sat result = Result::SAT_UNKNOWN;

  if(result == Result::SAT_UNKNOWN){
    if(exactResult){
      d_pivotBudget = -1;
    }else{
      d_pivotBudget = options::arithStandardCheckVarOrderPivots();
    }

    result = sumOfInfeasibilities();

    if(result ==  Result::UNSAT){
      ++(d_statistics.d_soiFoundUnsat);
      if(verbose){ Message() << "fc found unsat";}
    }else if(d_errorSet.errorEmpty()){
      ++(d_statistics.d_soiFoundSat);
      if(verbose){ Message() << "fc found model"; }
    }else{
      ++(d_statistics.d_soiMissed);
      if(verbose){ Message() << "fc missed"; }
    }
  }
  if(verbose){
    Message() << "(" << instance << ") pivots " << d_pivots << endl;
  }

  Assert(!d_errorSet.moreSignals());
  if(result == Result::SAT_UNKNOWN && d_errorSet.errorEmpty()){
    result = Result::SAT;
  }

  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Debug("soi::findModel") << "end findModel() " << instance << " " << result <<  endl;

  Assert(d_conflictVariables.empty());
  return result;
}


void SumOfInfeasibilitiesSPD::logPivot(WitnessImprovement w){
  if(d_pivotBudget > 0) {
    --d_pivotBudget;
  }
  Assert(w != AntiProductive);

  if(w == d_prevWitnessImprovement){
    ++d_witnessImprovementInARow;
    if(d_witnessImprovementInARow == 0){
      --d_witnessImprovementInARow;
    }
  }else{
    if(w != BlandsDegenerate){
      d_witnessImprovementInARow = 1;
    }
    d_prevWitnessImprovement = w;
  }
  if(strongImprovement(w)){
    d_leavingCountSinceImprovement.purge();
  }

  Debug("logPivot") << "logPivot " << d_prevWitnessImprovement << " "  << d_witnessImprovementInARow << endl;
}

uint32_t SumOfInfeasibilitiesSPD::degeneratePivotsInARow() const {
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

void SumOfInfeasibilitiesSPD::adjustFocusAndError(const UpdateInfo& up, const AVIntPairVec& focusChanges){
  uint32_t newErrorSize = d_errorSet.errorSize();
  adjustInfeasFunc(d_statistics.d_soiFocusConstructionTimer, d_soiVar, focusChanges);
  d_errorSize = newErrorSize;
}


UpdateInfo SumOfInfeasibilitiesSPD::selectUpdate(LinearEqualityModule::UpdatePreferenceFunction upf, LinearEqualityModule::VarPreferenceFunction bpf) {
  UpdateInfo selected;

  static int instance = 0 ;
  ++instance;

  Debug("soi::selectPrimalUpdate")
    << "selectPrimalUpdate " << instance << endl
    << d_soiVar << " " << d_tableau.basicRowLength(d_soiVar)
    << " " << d_linEq.debugBasicAtBoundCount(d_soiVar) << endl;

  typedef std::vector<Cand> CandVector;
  CandVector candidates;

  for(Tableau::RowIterator ri = d_tableau.basicRowIterator(d_soiVar); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;
    ArithVar curr = e.getColVar();
    if(curr == d_soiVar){ continue; }

    int sgn = e.getCoefficient().sgn();
    bool candidate =
      (sgn > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
      (sgn < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0);

    Debug("soi::selectPrimalUpdate")
      << "storing " << d_soiVar
      << " " << curr
      << " " << candidate
      << " " << e.getCoefficient()
      << " " << sgn << endl;

    if(candidate) {
      candidates.push_back(Cand(curr, 0, sgn, &e.getCoefficient()));
    }
  }

  CompPenaltyColLength colCmp(&d_linEq);
  CandVector::iterator i = candidates.begin();
  CandVector::iterator end = candidates.end();
  std::make_heap(i, end, colCmp);

  // For the first 3 pivots take the best
  // After that, once an improvement is found on look at a
  // small number of pivots after finding an improvement
  // the longer the search to more willing we are to look at more candidates
  int maxCandidatesAfterImprove =
    (d_pivots <= 2) ?  std::numeric_limits<int>::max() : d_pivots/5;

  int candidatesAfterFocusImprove = 0;
  while(i != end && candidatesAfterFocusImprove <= maxCandidatesAfterImprove){
    std::pop_heap(i, end, colCmp);
    --end;
    Cand& cand = (*end);
    ArithVar curr = cand.d_nb;
    const Rational& coeff = *cand.d_coeff;

    LinearEqualityModule::UpdatePreferenceFunction leavingPrefFunc = selectLeavingFunction(curr);
    UpdateInfo currProposal = d_linEq.speculativeUpdate(curr, coeff, leavingPrefFunc);

    Debug("soi::selectPrimalUpdate")
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
      Debug("soi::selectPrimalUpdate") << "selected " << w << endl;
      //setPenalty(curr, w);
      if(improvement(w)){
        bool exitEarly;
        switch(w){
        case ConflictFound: exitEarly = true; break;
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
      Debug("soi::selectPrimalUpdate") << "dropped "<< endl;
    }

  }
  return selected;
}

bool debugCheckWitness(const UpdateInfo& inf, WitnessImprovement w, bool useBlands){
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


void SumOfInfeasibilitiesSPD::debugPrintSignal(ArithVar updated) const{
  Debug("updateAndSignal") << "updated basic " << updated;
  Debug("updateAndSignal") << " length " << d_tableau.basicRowLength(updated);
  Debug("updateAndSignal") << " consistent " << d_variables.assignmentIsConsistent(updated);
  int dir = !d_variables.assignmentIsConsistent(updated) ?
    d_errorSet.getSgn(updated) : 0;
  Debug("updateAndSignal") << " dir " << dir;
  Debug("updateAndSignal") << " debugBasicAtBoundCount " << d_linEq.debugBasicAtBoundCount(updated) << endl;
}


void SumOfInfeasibilitiesSPD::updateAndSignal(const UpdateInfo& selected, WitnessImprovement w){
  ArithVar nonbasic = selected.nonbasic();

  static bool verbose = false;

  Debug("updateAndSignal") << "updateAndSignal " << selected << endl;

  stringstream ss;
  if(verbose){
    d_errorSet.debugPrint(ss);
    if(selected.describesPivot()){
      ArithVar leaving = selected.leaving();
      ss << "leaving " << leaving
         << " " << d_tableau.basicRowLength(leaving)
         << " " << d_linEq.debugBasicAtBoundCount(leaving)
         << endl;
    }
    if(degenerate(w) && selected.describesPivot()){
      ArithVar leaving = selected.leaving();
      Message()
        << "degenerate " << leaving
        << ", atBounds " << d_linEq.basicsAtBounds(selected)
        << ", len " << d_tableau.basicRowLength(leaving)
        << ", bc " << d_linEq.debugBasicAtBoundCount(leaving)
        << endl;
    }
  }

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
      if(Debug.isOn("updateAndSignal")){debugPrintSignal(updated);}
      if(!d_variables.assignmentIsConsistent(updated)){
        if(checkBasicForConflict(updated)){
          reportConflict(updated);
          //Assert(debugUpdatedBasic(selected, updated));
        }
      }
    }else{
      Debug("updateAndSignal") << "updated nonbasic " << updated << endl;
    }
    int currFocusSgn = d_errorSet.focusSgn(updated);
    if(currFocusSgn != prevFocusSgn){
      int change = currFocusSgn - prevFocusSgn;
      focusChanges.push_back(make_pair(updated, change));
    }
  }

  if(verbose){
    Message() << "conflict variable " << selected << endl;
    Message() << ss.str();
  }
  if(Debug.isOn("error")){ d_errorSet.debugPrint(Debug("error")); }

  //Assert(debugSelectedErrorDropped(selected, d_errorSize, d_errorSet.errorSize()));

  adjustFocusAndError(selected, focusChanges);
}

void SumOfInfeasibilitiesSPD::qeAddRange(uint32_t begin, uint32_t end){
  Assert(!d_qeInSoi.empty());
  for(uint32_t i = begin; i != end; ++i){
    ArithVar v = d_qeConflict[i];
    addToInfeasFunc(d_statistics.d_soiConflictMinimization, d_soiVar, v);
    d_qeInSoi.add(v);
  }
}

void SumOfInfeasibilitiesSPD::qeRemoveRange(uint32_t begin, uint32_t end){
  for(uint32_t i = begin; i != end; ++i){
    ArithVar v = d_qeConflict[i];
    removeFromInfeasFunc(d_statistics.d_soiConflictMinimization, d_soiVar, v);
    d_qeInSoi.remove(v);
  }
  Assert(!d_qeInSoi.empty());
}

void SumOfInfeasibilitiesSPD::qeSwapRange(uint32_t N, uint32_t r, uint32_t s){
  for(uint32_t i = 0; i < N; ++i){
    std::swap(d_qeConflict[r+i], d_qeConflict[s+i]);
  }
}

/**
 * Region notation:
 * A region is either
 *  - A single element X@i with the name X at the position i
 *  - A sequence of indices X@[i,j) with the name X and the elements between i [inclusive] and j exclusive
 *  - A concatenation of regions R1 and R2, R1;R2
 *
 * Given the fixed assumptions C @ [0,cEnd) and a set of candidate minimizations U@[cEnd, uEnd)
 * s.t. C \cup U is known to be in conflict ([0,uEnd) has a conflict), find a minimal
 * subset of U, Delta, s.t. C \cup Delta is in conflict.
 *
 * Pre:
 *  [0, uEnd) is a set and is in conflict.
 *    uEnd <= assumptions.size()
 *  [0, cEnd) is in d_inSoi.
 *
 * Invariants: [0,cEnd) is never modified
 *
 * Post:
 *  [0, cEnd); [cEnd, deltaEnd) is in conflict
 *  [0, deltaEnd) is a set
 *  [0, deltaEnd) is in d_inSoi
 */
uint32_t SumOfInfeasibilitiesSPD::quickExplainRec(uint32_t cEnd, uint32_t uEnd){
  Assert(cEnd <= uEnd);
  Assert(d_qeInUAndNotInSoi.empty());
  Assert(d_qeGreedyOrder.empty());

  const Tableau::Entry* spoiler = NULL;

  if(d_soiVar != ARITHVAR_SENTINEL && d_linEq.selectSlackEntry(d_soiVar, false) == NULL){
    // already in conflict
    return cEnd;
  }

  Assert(cEnd < uEnd);

  // Phase 1 : Construct the conflict greedily

  for(uint32_t i = cEnd; i < uEnd; ++i){
    d_qeInUAndNotInSoi.add(d_qeConflict[i]);
  }
  if(d_soiVar == ARITHVAR_SENTINEL){ // special case for d_soiVar being empty
    ArithVar first = d_qeConflict[cEnd];
    d_soiVar = constructInfeasiblityFunction(d_statistics.d_soiConflictMinimization, first);
    d_qeInSoi.add(first);
    d_qeInUAndNotInSoi.remove(first);
    d_qeGreedyOrder.push_back(first);
  }
  while((spoiler = d_linEq.selectSlackEntry(d_soiVar, false)) != NULL){
    Assert(!d_qeInUAndNotInSoi.empty());

    ArithVar nb = spoiler->getColVar();
    int oppositeSgn = -(spoiler->getCoefficient().sgn());
    Assert(oppositeSgn != 0);

    ArithVar basicWithOp = find_basic_in_sgns(d_qeSgns, nb, oppositeSgn, d_qeInUAndNotInSoi, true);
    Assert(basicWithOp != ARITHVAR_SENTINEL);

    addToInfeasFunc(d_statistics.d_soiConflictMinimization, d_soiVar, basicWithOp);
    d_qeInSoi.add(basicWithOp);
    d_qeInUAndNotInSoi.remove(basicWithOp);
    d_qeGreedyOrder.push_back(basicWithOp);
  }
  Assert(spoiler == NULL);

  // Compact the set u
  uint32_t newEnd = cEnd + d_qeGreedyOrder.size();
  std::copy(d_qeGreedyOrder.begin(), d_qeGreedyOrder.end(), d_qeConflict.begin()+cEnd);

  d_qeInUAndNotInSoi.purge();
  d_qeGreedyOrder.clear();

   // Phase 2 : Recursively determine the minimal set of rows

  uint32_t xPos = cEnd;
  std::swap(d_qeGreedyOrder[xPos], d_qeGreedyOrder[newEnd - 1]);
  uint32_t uBegin = xPos + 1;
  uint32_t split = (newEnd - uBegin)/2 + uBegin;

  //assumptions : C @ [0, cEnd); X @ xPos; U1 @ [u1Begin, split); U2 @ [split, newEnd)
  // [0, newEnd) == d_inSoi

  uint32_t compactU2;
  if(split == newEnd){ // U2 is empty
    compactU2 = newEnd;
  }else{
    // Remove U2 from Soi
    qeRemoveRange(split, newEnd);
    // [0, split) == d_inSoi

    // pre assumptions: C + X + U1 @ [0,split); U2 [split, newEnd)
    compactU2 = quickExplainRec(split, newEnd);
    // post:
    //  assumptions: C + X + U1 @ [0, split); delta2 @ [split - compactU2)
    //  d_inSoi = [0, compactU2)
  }
  uint32_t deltaSize = compactU2 - split;
  qeSwapRange(deltaSize, uBegin, split);
  uint32_t d2End = uBegin+deltaSize;
  // assumptions : C @ [0, cEnd); X @ xPos; delta2 @ [uBegin, d2End); U1 @ [d2End, compactU2)
  //  d_inSoi == [0, compactU2)

  uint32_t d1End;
  if(d2End == compactU2){ // U1 is empty
    d1End = d2End;
  }else{
    qeRemoveRange(d2End, compactU2);

    //pre assumptions : C + X + delta2 @ [0, d2End); U1 @ [d2End, compactU2);
    d1End = quickExplainRec(d2End, compactU2);
    //post:
    // assumptions : C + X + delta2 @ [0, d2End); delta1 @ [d2End, d1End);
    // d_inSoi = [0, d1End)
  }
  //After both:
  // d_inSoi == [0, d1End), C @ [0, cEnd); X + delta2 + delta 1 @ [xPos, d1End);

  Assert(d_qeInUAndNotInSoi.empty());
  Assert(d_qeGreedyOrder.empty());
  return d1End;
}

void SumOfInfeasibilitiesSPD::quickExplain(){
  Assert(d_qeInSoi.empty());
  Assert(d_qeInUAndNotInSoi.empty());
  Assert(d_qeGreedyOrder.empty());
  Assert(d_soiVar == ARITHVAR_SENTINEL);
  Assert(d_qeSgns.empty());

  d_qeConflict.clear();
  d_errorSet.pushFocusInto(d_qeConflict);

  //cout <<  d_qeConflict.size() << " ";
  uint32_t size = d_qeConflict.size();

  if(size > 2){
    for(ErrorSet::focus_iterator iter = d_errorSet.focusBegin(), end = d_errorSet.focusEnd(); iter != end; ++iter){
      ArithVar e = *iter;
      addRowSgns(d_qeSgns, e, d_errorSet.getSgn(e));
    }
    uint32_t end = quickExplainRec(0u, size);
    Assert(end <= d_qeConflict.size());
    Assert(d_soiVar != ARITHVAR_SENTINEL);
    Assert(!d_qeInSoi.empty());

    d_qeConflict.resize(end);
    tearDownInfeasiblityFunction(d_statistics.d_soiConflictMinimization, d_soiVar);
    d_soiVar = ARITHVAR_SENTINEL;
    d_qeInSoi.purge();
    d_qeSgns.clear();
  }

  //cout << d_qeConflict.size() << endl;

  Assert(d_qeInSoi.empty());
  Assert(d_qeInUAndNotInSoi.empty());
  Assert(d_qeGreedyOrder.empty());
  Assert(d_soiVar == ARITHVAR_SENTINEL);
  Assert(d_qeSgns.empty());
}

unsigned SumOfInfeasibilitiesSPD::trySet(const ArithVarVec& set){
  Assert(d_soiVar == ARITHVAR_SENTINEL);
  bool success = false;
  if(set.size() >= 2){
    d_soiVar = constructInfeasiblityFunction(d_statistics.d_soiConflictMinimization, set);
    success = d_linEq.selectSlackEntry(d_soiVar, false) == NULL;

    tearDownInfeasiblityFunction(d_statistics.d_soiConflictMinimization, d_soiVar);
    d_soiVar = ARITHVAR_SENTINEL;
  }
  return success ? set.size() : std::numeric_limits<int>::max();
}

std::vector< ArithVarVec > SumOfInfeasibilitiesSPD::greedyConflictSubsets(){
  Debug("arith::greedyConflictSubsets") << "greedyConflictSubsets start" << endl;

  std::vector< ArithVarVec > subsets;
  Assert(d_soiVar == ARITHVAR_SENTINEL);

  if(d_errorSize <= 2){
    ArithVarVec inError;
    d_errorSet.pushFocusInto(inError);

    Assert(debugIsASet(inError));
    subsets.push_back(inError);
    return subsets;
  }
  Assert(d_errorSize > 2);

  //sgns_table< <nonbasic,sgn>, [basics] >;
  // Phase 0: Construct the sgns table
  sgn_table sgns;
  DenseSet hasParticipated; //Has participated in a conflict
  for(ErrorSet::focus_iterator iter = d_errorSet.focusBegin(), end = d_errorSet.focusEnd(); iter != end; ++iter){
    ArithVar e = *iter;
    addRowSgns(sgns, e, d_errorSet.getSgn(e));

    Debug("arith::greedyConflictSubsets") << "basic error var: " << e << endl;
    if(Debug.isOn("arith::greedyConflictSubsets")){
      d_tableau.debugPrintIsBasic(e);
      d_tableau.printBasicRow(e, Debug("arith::greedyConflictSubsets"));
    }
  }

  // Phase 1: Try to find at least 1 pair for every element
  ArithVarVec tmp;
  tmp.push_back(0);
  tmp.push_back(0);
  for(ErrorSet::focus_iterator iter = d_errorSet.focusBegin(), end = d_errorSet.focusEnd(); iter != end; ++iter){
    ArithVar e = *iter;
    tmp[0] = e;

    int errSgn = d_errorSet.getSgn(e);
    bool decreasing = errSgn < 0;
    const Tableau::Entry* spoiler = d_linEq.selectSlackEntry(e, decreasing);
    Assert(spoiler != NULL);
    ArithVar nb = spoiler->getColVar();
    int oppositeSgn = -(errSgn * (spoiler->getCoefficient().sgn()));

    sgn_table::const_iterator opposites = find_sgns(sgns, nb, oppositeSgn);
    Assert(opposites != sgns.end());

    const ArithVarVec& choices = (*opposites).second;
    for(ArithVarVec::const_iterator j = choices.begin(), jend = choices.end(); j != jend; ++j){
      ArithVar b = *j;
      if(b < e){ continue; }
      tmp[0] = e;
      tmp[1] = b;
      if(trySet(tmp) == 2){
        Debug("arith::greedyConflictSubsets")  << "found a pair " << b << " " << e << endl;
        hasParticipated.softAdd(b);
        hasParticipated.softAdd(e);
        Assert(debugIsASet(tmp));
        subsets.push_back(tmp);
        ++(d_statistics.d_soiConflicts);
        ++(d_statistics.d_hasToBeMinimal);
      }
    }
  }


  // Phase 2: If there is a variable that has not participated attempt to start a conflict
  ArithVarVec possibleStarts; //List of elements that can be tried for starts.
  d_errorSet.pushFocusInto(possibleStarts);
  while(!possibleStarts.empty()){
    Assert(d_soiVar == ARITHVAR_SENTINEL);

    ArithVar v = possibleStarts.back();
    possibleStarts.pop_back();
    if(hasParticipated.isMember(v)){ continue; }

    hasParticipated.add(v);

    Assert(d_soiVar == ARITHVAR_SENTINEL);
    //d_soiVar's row =  \sumofinfeasibilites underConstruction
    ArithVarVec underConstruction;
    underConstruction.push_back(v);
    d_soiVar = constructInfeasiblityFunction(d_statistics.d_soiConflictMinimization, v);

    Debug("arith::greedyConflictSubsets") << "trying " << v << endl;

    const Tableau::Entry* spoiler = NULL;
    while( (spoiler = d_linEq.selectSlackEntry(d_soiVar, false)) != NULL){
      ArithVar nb = spoiler->getColVar();
      int oppositeSgn = -(spoiler->getCoefficient().sgn());
      Assert(oppositeSgn != 0);

      Debug("arith::greedyConflictSubsets") << "looking for " << nb << " " << oppositeSgn << endl;

      ArithVar basicWithOp = find_basic_in_sgns(sgns, nb, oppositeSgn, hasParticipated, false);

      if(basicWithOp == ARITHVAR_SENTINEL){
        Debug("arith::greedyConflictSubsets") << "search did not work  for " << nb << endl;
        // greedy construction has failed
        break;
      }else{
        Debug("arith::greedyConflictSubsets") << "found  " << basicWithOp << endl;

        addToInfeasFunc(d_statistics.d_soiConflictMinimization, d_soiVar, basicWithOp);
        hasParticipated.softAdd(basicWithOp);
        underConstruction.push_back(basicWithOp);
      }
    }
    if(spoiler == NULL){
      Debug("arith::greedyConflictSubsets") << "success" << endl;
      //then underConstruction contains a conflicting subset
      Assert(debugIsASet(underConstruction));
      subsets.push_back(underConstruction);
      ++d_statistics.d_soiConflicts;
      if(underConstruction.size() == 3){
        ++d_statistics.d_hasToBeMinimal;
      }else{
        ++d_statistics.d_maybeNotMinimal;
      }
    }else{
      Debug("arith::greedyConflictSubsets") << "failure" << endl;
    }
    tearDownInfeasiblityFunction(d_statistics.d_soiConflictMinimization, d_soiVar);
    d_soiVar = ARITHVAR_SENTINEL;
    // if(false && spoiler == NULL){
    //   ArithVarVec tmp;
    //   int smallest = tryAllSubsets(underConstruction, 0, tmp);
    //   cout << underConstruction.size() << " " << smallest << endl;
    //   Assert(smallest >= underConstruction.size());
    //   if(smallest < underConstruction.size()){
    //     exit(-1);
    //   }
    // }
  }

  Assert(d_soiVar == ARITHVAR_SENTINEL);
  Debug("arith::greedyConflictSubsets") << "greedyConflictSubsets done" << endl;
  return subsets;
}

bool SumOfInfeasibilitiesSPD::generateSOIConflict(const ArithVarVec& subset){
  Assert(d_soiVar == ARITHVAR_SENTINEL);
  d_soiVar = constructInfeasiblityFunction(d_statistics.d_soiConflictMinimization, subset);
  Assert(!subset.empty());
  Assert(!d_conflictBuilder->underConstruction());

  Debug("arith::generateSOIConflict") << "SumOfInfeasibilitiesSPD::generateSOIConflict(...) start" << endl;

  bool success = false;
    
  for(ArithVarVec::const_iterator iter = subset.begin(), end = subset.end(); iter != end; ++iter){
    ArithVar e = *iter;
    ConstraintP violated = d_errorSet.getViolated(e);
    Assert(violated != NullConstraint);

    int sgn = d_errorSet.getSgn(e);
    const Rational& violatedCoeff = sgn > 0 ? d_negOne : d_posOne;
    Debug("arith::generateSOIConflict") << "basic error var: "
                                        << "(" <<  violatedCoeff << ")"
                                        << " " << violated
                                        << endl;


    d_conflictBuilder->addConstraint(violated, violatedCoeff);
    Assert(violated->hasProof());
    if(!success && !violated->negationHasProof()){
      success = true;
      d_conflictBuilder->makeLastConsequent();
    }
  }
  
  if(!success){
    // failure
    d_conflictBuilder->reset();
  } else {
    // pick a violated constraint arbitrarily. any of them may be selected for the conflict
    Assert(d_conflictBuilder->underConstruction());
    Assert(d_conflictBuilder->consequentIsSet());

    for(Tableau::RowIterator i = d_tableau.basicRowIterator(d_soiVar); !i.atEnd(); ++i){
      const Tableau::Entry& entry = *i;
      ArithVar v = entry.getColVar();
      if(v == d_soiVar){ continue; }
      const Rational& coeff = entry.getCoefficient();

      ConstraintP c = (coeff.sgn() > 0) ?
        d_variables.getUpperBoundConstraint(v) :
        d_variables.getLowerBoundConstraint(v);
      
      Debug("arith::generateSOIConflict") << "non-basic var: "
                                          << "(" <<  coeff << ")"
                                          << " " << c
                                          << endl;
      d_conflictBuilder->addConstraint(c, coeff);
    }
    ConstraintCP conflicted = d_conflictBuilder->commitConflict();
    d_conflictChannel.raiseConflict(conflicted);
  }

  tearDownInfeasiblityFunction(d_statistics.d_soiConflictMinimization, d_soiVar);
  d_soiVar = ARITHVAR_SENTINEL;
  Debug("arith::generateSOIConflict") << "SumOfInfeasibilitiesSPD::generateSOIConflict(...) done" << endl;
  Assert(d_soiVar == ARITHVAR_SENTINEL);
  Assert(!d_conflictBuilder->underConstruction());
  return success;
}


WitnessImprovement SumOfInfeasibilitiesSPD::SOIConflict(){
  static int instance = 0;
  instance++;
  
  Debug("arith::SOIConflict") << "SumOfInfeasibilitiesSPD::SOIConflict() start "
                              << instance << ": |E| = " << d_errorSize << endl;
  if(Debug.isOn("arith::SOIConflict")){
    d_errorSet.debugPrint(cout);
  }
  Debug("arith::SOIConflict") << endl;

  tearDownInfeasiblityFunction(d_statistics.d_soiConflictMinimization, d_soiVar);
  d_soiVar = ARITHVAR_SENTINEL;

  if(options::soiQuickExplain()){
    quickExplain();
    generateSOIConflict(d_qeConflict);
  }else{
    vector<ArithVarVec> subsets = greedyConflictSubsets();
    Assert(d_soiVar == ARITHVAR_SENTINEL);
    bool anySuccess = false;
    Assert(!subsets.empty());
    for(vector<ArithVarVec>::const_iterator i = subsets.begin(), end = subsets.end(); i != end; ++i){
      const ArithVarVec& subset = *i;
      Assert(debugIsASet(subset));
      anySuccess = generateSOIConflict(subset) || anySuccess;
      //Node conflict = generateSOIConflict(subset);
      //cout << conflict << endl;

      //reportConflict(conf); do not do this. We need a custom explanations!
      //d_conflictChannel(conflict);
    }
    Assert(anySuccess);
  }
  Assert(d_soiVar == ARITHVAR_SENTINEL);
  d_soiVar = constructInfeasiblityFunction(d_statistics.d_soiConflictMinimization);

  //reportConflict(conf); do not do this. We need a custom explanations!
  d_conflictVariables.add(d_soiVar);

  Debug("arith::SOIConflict") << "SumOfInfeasibilitiesSPD::SOIConflict() done "
                              << instance << "end" << endl;
  return ConflictFound;
}

WitnessImprovement SumOfInfeasibilitiesSPD::soiRound() {
  Assert(d_soiVar != ARITHVAR_SENTINEL);

  bool useBlands = degeneratePivotsInARow() >= s_maxDegeneratePivotsBeforeBlandsOnLeaving;
  LinearEqualityModule::UpdatePreferenceFunction upf;
  if(useBlands) {
    upf = &LinearEqualityModule::preferWitness<false>;
  } else {
    upf = &LinearEqualityModule::preferWitness<true>;
  }

  LinearEqualityModule::VarPreferenceFunction bpf = useBlands ?
    &LinearEqualityModule::minVarOrder :
    &LinearEqualityModule::minRowLength;
  bpf = &LinearEqualityModule::minVarOrder;

  UpdateInfo selected = selectUpdate(upf, bpf);

  if(selected.uninitialized()){
    Debug("selectFocusImproving") << "SOI is optimum, but we don't have sat/conflict yet" << endl;
    return SOIConflict();
  }else{
    Assert(!selected.uninitialized());
    WitnessImprovement w = selected.getWitness(false);
    Assert(debugCheckWitness(selected, w, false));

    updateAndSignal(selected, w);
    logPivot(w);
    return w;
  }
}

bool SumOfInfeasibilitiesSPD::debugSOI(WitnessImprovement w, ostream& out, int instance) const{
  return true;
  // out << "DLV("<<instance<<") ";
  // switch(w){
  // case ConflictFound:
  //   out << "found conflict" << endl;
  //   return !d_conflictVariables.empty();
  // case ErrorDropped:
  //   return false;
  //   // out << "dropped " << prevErrorSize - d_errorSize << endl;
  //   // return d_errorSize < prevErrorSize;
  // case FocusImproved:
  //   out << "focus improved"<< endl;
  //   return d_errorSize == prevErrorSize;
  // case FocusShrank:
  //   Unreachable();
  //   return false;
  // case BlandsDegenerate:
  //   out << "bland degenerate"<< endl;
  //   return true;
  // case HeuristicDegenerate:
  //   out << "heuristic degenerate"<< endl;
  //   return true;
  // case AntiProductive:
  // case Degenerate:
  //   return false;
  // }
  // return false;
}

Result::Sat SumOfInfeasibilitiesSPD::sumOfInfeasibilities(){
  static int instance = 0;
  static bool verbose = false;

  TimerStat::CodeTimer codeTimer(d_statistics.d_soiTimer);

  Assert(d_sgnDisagreements.empty());
  Assert(d_pivotBudget != 0);
  Assert(d_errorSize == d_errorSet.errorSize());
  Assert(d_errorSize > 0);
  Assert(d_conflictVariables.empty());
  Assert(d_soiVar == ARITHVAR_SENTINEL);

  //d_scores.purge();
  d_soiVar = constructInfeasiblityFunction(d_statistics.d_soiFocusConstructionTimer);


  while(d_pivotBudget != 0  && d_errorSize > 0 && d_conflictVariables.empty()){
    ++instance;
    Debug("dualLike") << "dualLike " << instance << endl;

    Assert(d_errorSet.noSignals());
    // Possible outcomes:
    // - conflict
    // - budget was exhausted
    // - focus went down
    Debug("dualLike") << "selectFocusImproving " << endl;
    WitnessImprovement w = soiRound();

    Assert(d_errorSize == d_errorSet.errorSize());

    if(verbose){
      debugSOI(w,  Message(), instance);
    }
    Assert(debugSOI(w, Debug("dualLike"), instance));
  }


  if(d_soiVar != ARITHVAR_SENTINEL){
    tearDownInfeasiblityFunction(d_statistics.d_soiFocusConstructionTimer, d_soiVar);
    d_soiVar = ARITHVAR_SENTINEL;
  }

  Assert(d_soiVar == ARITHVAR_SENTINEL);
  if(!d_conflictVariables.empty()){
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Assert(d_errorSet.noSignals());
    return Result::SAT;
  }else{
    Assert(d_pivotBudget == 0);
    return Result::SAT_UNKNOWN;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
