/*********************                                                        */
/*! \file simplex.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/simplex.h"
#include "theory/arith/options.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;

static const bool CHECK_AFTER_PIVOT = true;

SimplexDecisionProcedure::SimplexDecisionProcedure(LinearEqualityModule& linEq, NodeCallBack& conflictChannel, ArithVarMalloc& malloc, ConstraintDatabase& cd) :
  d_conflictVariable(ARITHVAR_SENTINEL),
  d_linEq(linEq),
  d_partialModel(d_linEq.getPartialModel()),
  d_tableau(d_linEq.getTableau()),
  d_queue(d_partialModel, d_tableau),
  d_numVariables(0),
  d_conflictChannel(conflictChannel),
  d_pivotsInRound(),
  d_DELTA_ZERO(0,0),
  d_arithVarMalloc(malloc),
  d_constraintDatabase(cd),
  d_optRow(ARITHVAR_SENTINEL),
  d_negOptConstant(d_DELTA_ZERO)
{
  switch(ArithHeuristicPivotRule rule = options::arithHeuristicPivotRule()) {
  case MINIMUM:
    d_queue.setPivotRule(ArithPriorityQueue::MINIMUM);
    break;
  case BREAK_TIES:
    d_queue.setPivotRule(ArithPriorityQueue::BREAK_TIES);
    break;
  case MAXIMUM:
    d_queue.setPivotRule(ArithPriorityQueue::MAXIMUM);
    break;
  default:
    Unhandled(rule);
  }

  srand(62047);
}

SimplexDecisionProcedure::Statistics::Statistics():
  d_statUpdateConflicts("theory::arith::UpdateConflicts", 0),
  d_findConflictOnTheQueueTime("theory::arith::findConflictOnTheQueueTime"),
  d_attemptBeforeDiffSearch("theory::arith::qi::BeforeDiffSearch::attempt",0),
  d_successBeforeDiffSearch("theory::arith::qi::BeforeDiffSearch::success",0),
  d_attemptAfterDiffSearch("theory::arith::qi::AfterDiffSearch::attempt",0),
  d_successAfterDiffSearch("theory::arith::qi::AfterDiffSearch::success",0),
  d_attemptDuringDiffSearch("theory::arith::qi::DuringDiffSearch::attempt",0),
  d_successDuringDiffSearch("theory::arith::qi::DuringDiffSearch::success",0),
  d_attemptDuringVarOrderSearch("theory::arith::qi::DuringVarOrderSearch::attempt",0),
  d_successDuringVarOrderSearch("theory::arith::qi::DuringVarOrderSearch::success",0),
  d_attemptAfterVarOrderSearch("theory::arith::qi::AfterVarOrderSearch::attempt",0),
  d_successAfterVarOrderSearch("theory::arith::qi::AfterVarOrderSearch::success",0),
  d_weakeningAttempts("theory::arith::weakening::attempts",0),
  d_weakeningSuccesses("theory::arith::weakening::success",0),
  d_weakenings("theory::arith::weakening::total",0),
  d_weakenTime("theory::arith::weakening::time"),
  d_simplexConflicts("theory::arith::simplexConflicts",0),
  // primal
  d_primalTimer("theory::arith::primal::overall::timer"),
  d_internalTimer("theory::arith::primal::internal::timer"),
  d_primalCalls("theory::arith::primal::calls",0),
  d_primalSatCalls("theory::arith::primal::calls::sat",0),
  d_primalUnsatCalls("theory::arith::primal::calls::unsat",0),
  d_primalPivots("theory::arith::primal::pivots",0),
  d_primalImprovingPivots("theory::arith::primal::pivots::improving",0),
  d_primalThresholdReachedPivot("theory::arith::primal::thresholds",0),
  d_primalThresholdReachedPivot_dropped("theory::arith::primal::thresholds::dropped",0),
  d_primalReachedMaxPivots("theory::arith::primal::maxpivots",0),
  d_primalReachedMaxPivots_contractMadeProgress("theory::arith::primal::maxpivots::contract",0),
  d_primalReachedMaxPivots_checkForConflictWorked("theory::arith::primal::maxpivots::checkworked",0),
  d_primalGlobalMinimum("theory::arith::primal::minimum",0),
  d_primalGlobalMinimum_rowConflictWorked("theory::arith::primal::minimum::checkworked",0),
  d_primalGlobalMinimum_firstHalfWasSat("theory::arith::primal::minimum::firsthalf::sat",0),
  d_primalGlobalMinimum_firstHalfWasUnsat("theory::arith::primal::minimum::firsthalf::unsat",0),
  d_primalGlobalMinimum_contractMadeProgress("theory::arith::primal::minimum::progress",0),
  d_unboundedFound("theory::arith::primal::unbounded",0),
  d_unboundedFound_drive("theory::arith::primal::unbounded::drive",0),
  d_unboundedFound_dropped("theory::arith::primal::unbounded::dropped",0)
{
  StatisticsRegistry::registerStat(&d_statUpdateConflicts);

  StatisticsRegistry::registerStat(&d_findConflictOnTheQueueTime);

  StatisticsRegistry::registerStat(&d_attemptBeforeDiffSearch);
  StatisticsRegistry::registerStat(&d_successBeforeDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptAfterDiffSearch);
  StatisticsRegistry::registerStat(&d_successAfterDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptDuringDiffSearch);
  StatisticsRegistry::registerStat(&d_successDuringDiffSearch);
  StatisticsRegistry::registerStat(&d_attemptDuringVarOrderSearch);
  StatisticsRegistry::registerStat(&d_successDuringVarOrderSearch);
  StatisticsRegistry::registerStat(&d_attemptAfterVarOrderSearch);
  StatisticsRegistry::registerStat(&d_successAfterVarOrderSearch);

  StatisticsRegistry::registerStat(&d_weakeningAttempts);
  StatisticsRegistry::registerStat(&d_weakeningSuccesses);
  StatisticsRegistry::registerStat(&d_weakenings);
  StatisticsRegistry::registerStat(&d_weakenTime);

  StatisticsRegistry::registerStat(&d_simplexConflicts);

  //primal  
  StatisticsRegistry::registerStat(&d_primalTimer);
  StatisticsRegistry::registerStat(&d_internalTimer);

  StatisticsRegistry::registerStat(&d_primalCalls);
  StatisticsRegistry::registerStat(&d_primalSatCalls);
  StatisticsRegistry::registerStat(&d_primalUnsatCalls);

  StatisticsRegistry::registerStat(&d_primalPivots);
  StatisticsRegistry::registerStat(&d_primalImprovingPivots);

  StatisticsRegistry::registerStat(&d_primalThresholdReachedPivot);
  StatisticsRegistry::registerStat(&d_primalThresholdReachedPivot_dropped);
    
  StatisticsRegistry::registerStat(&d_primalReachedMaxPivots);
  StatisticsRegistry::registerStat(&d_primalReachedMaxPivots_contractMadeProgress);
  StatisticsRegistry::registerStat(&d_primalReachedMaxPivots_checkForConflictWorked);

    
  StatisticsRegistry::registerStat(&d_primalGlobalMinimum);
  StatisticsRegistry::registerStat(&d_primalGlobalMinimum_rowConflictWorked);
  StatisticsRegistry::registerStat(&d_primalGlobalMinimum_firstHalfWasSat);
  StatisticsRegistry::registerStat(&d_primalGlobalMinimum_firstHalfWasUnsat);
  StatisticsRegistry::registerStat(&d_primalGlobalMinimum_contractMadeProgress);

  
  StatisticsRegistry::registerStat(&d_unboundedFound);
  StatisticsRegistry::registerStat(&d_unboundedFound_drive);
  StatisticsRegistry::registerStat(&d_unboundedFound_dropped);

}

SimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statUpdateConflicts);

  StatisticsRegistry::unregisterStat(&d_findConflictOnTheQueueTime);

  StatisticsRegistry::unregisterStat(&d_attemptBeforeDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successBeforeDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptAfterDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successAfterDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptDuringDiffSearch);
  StatisticsRegistry::unregisterStat(&d_successDuringDiffSearch);
  StatisticsRegistry::unregisterStat(&d_attemptDuringVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_successDuringVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_attemptAfterVarOrderSearch);
  StatisticsRegistry::unregisterStat(&d_successAfterVarOrderSearch);

  StatisticsRegistry::unregisterStat(&d_weakeningAttempts);
  StatisticsRegistry::unregisterStat(&d_weakeningSuccesses);
  StatisticsRegistry::unregisterStat(&d_weakenings);
  StatisticsRegistry::unregisterStat(&d_weakenTime);

  StatisticsRegistry::unregisterStat(&d_simplexConflicts);

  //primal
  StatisticsRegistry::unregisterStat(&d_primalTimer);
  StatisticsRegistry::unregisterStat(&d_internalTimer);

  StatisticsRegistry::unregisterStat(&d_primalCalls);
  StatisticsRegistry::unregisterStat(&d_primalSatCalls);
  StatisticsRegistry::unregisterStat(&d_primalUnsatCalls);

  StatisticsRegistry::unregisterStat(&d_primalPivots);
  StatisticsRegistry::unregisterStat(&d_primalImprovingPivots);

  StatisticsRegistry::unregisterStat(&d_primalThresholdReachedPivot);
  StatisticsRegistry::unregisterStat(&d_primalThresholdReachedPivot_dropped);
    
  StatisticsRegistry::unregisterStat(&d_primalReachedMaxPivots);
  StatisticsRegistry::unregisterStat(&d_primalReachedMaxPivots_contractMadeProgress);
  StatisticsRegistry::unregisterStat(&d_primalReachedMaxPivots_checkForConflictWorked);

    
  StatisticsRegistry::unregisterStat(&d_primalGlobalMinimum);
  StatisticsRegistry::unregisterStat(&d_primalGlobalMinimum_rowConflictWorked);
  StatisticsRegistry::unregisterStat(&d_primalGlobalMinimum_firstHalfWasSat);
  StatisticsRegistry::unregisterStat(&d_primalGlobalMinimum_firstHalfWasUnsat);
  StatisticsRegistry::unregisterStat(&d_primalGlobalMinimum_contractMadeProgress);

  StatisticsRegistry::unregisterStat(&d_unboundedFound);
  StatisticsRegistry::unregisterStat(&d_unboundedFound_drive);
  StatisticsRegistry::unregisterStat(&d_unboundedFound_dropped);
}




ArithVar SimplexDecisionProcedure::minVarOrder(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  // Assert(!simp.d_tableau.isBasic(x));
  // Assert(!simp.d_tableau.isBasic(y));
  if(x <= y){
    return x;
  } else {
    return y;
  }
}

ArithVar SimplexDecisionProcedure::minColLength(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!simp.d_tableau.isBasic(x));
  Assert(!simp.d_tableau.isBasic(y));
  uint32_t xLen = simp.d_tableau.getColLength(x);
  uint32_t yLen = simp.d_tableau.getColLength(y);
  if( xLen > yLen){
     return y;
  } else if( xLen== yLen ){
    return minVarOrder(simp,x,y);
  }else{
    return x;
  }
}

ArithVar SimplexDecisionProcedure::minRowLength(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(simp.d_tableau.isBasic(x));
  Assert(simp.d_tableau.isBasic(y));
  uint32_t xLen = simp.d_tableau.getRowLength(simp.d_tableau.basicToRowIndex(x));
  uint32_t yLen = simp.d_tableau.getRowLength(simp.d_tableau.basicToRowIndex(y));
  if( xLen > yLen){
     return y;
  } else if( xLen == yLen ){
    return minVarOrder(simp,x,y);
  }else{
    return x;
  }
}
ArithVar SimplexDecisionProcedure::minBoundAndRowCount(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!simp.d_tableau.isBasic(x));
  Assert(!simp.d_tableau.isBasic(y));
  if(simp.d_partialModel.hasEitherBound(x) && !simp.d_partialModel.hasEitherBound(y)){
    return y;
  }else if(!simp.d_partialModel.hasEitherBound(x) && simp.d_partialModel.hasEitherBound(y)){
    return x;
  }else {
    return minColLength(simp, x, y);
  }
}

template <bool above>
ArithVar SimplexDecisionProcedure::selectSlack(ArithVar x_i, SimplexDecisionProcedure::PreferenceFunction pref){
  ArithVar slack = ARITHVAR_SENTINEL;

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd();  ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = entry.getCoefficient();
    int sgn = a_ij.sgn();
    if(isAcceptableSlack<above>(sgn, nonbasic)){
      //If one of the above conditions is met, we have found an acceptable
      //nonbasic variable to pivot x_i with.  We can now choose which one we
      //prefer the most.
      slack = (slack == ARITHVAR_SENTINEL) ? nonbasic : pref(*this, slack, nonbasic);
    }
  }

  return slack;
}

Node betterConflict(TNode x, TNode y){
  if(x.isNull()) return y;
  else if(y.isNull()) return x;
  else if(x.getNumChildren() <= y.getNumChildren()) return x;
  else return y;
}

bool SimplexDecisionProcedure::findConflictOnTheQueue(SearchPeriod type) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_findConflictOnTheQueueTime);
  Assert(d_successes.empty());

  switch(type){
  case BeforeDiffSearch:     ++(d_statistics.d_attemptBeforeDiffSearch); break;
  case DuringDiffSearch:     ++(d_statistics.d_attemptDuringDiffSearch); break;
  case AfterDiffSearch:      ++(d_statistics.d_attemptAfterDiffSearch); break;
  case DuringVarOrderSearch: ++(d_statistics.d_attemptDuringVarOrderSearch); break;
  case AfterVarOrderSearch:  ++(d_statistics.d_attemptAfterVarOrderSearch); break;
  }

  ArithPriorityQueue::const_iterator i = d_queue.begin();
  ArithPriorityQueue::const_iterator end = d_queue.end();
  for(; i != end; ++i){
    ArithVar x_i = *i;

    if(x_i != d_conflictVariable && d_tableau.isBasic(x_i) && !d_successes.isMember(x_i)){
      Node possibleConflict = checkBasicForConflict(x_i);
      if(!possibleConflict.isNull()){
        d_successes.add(x_i);
        reportConflict(possibleConflict);
      }
    }
  }
  if(!d_successes.empty()){
    switch(type){
    case BeforeDiffSearch:     ++(d_statistics.d_successBeforeDiffSearch); break;
    case DuringDiffSearch:     ++(d_statistics.d_successDuringDiffSearch); break;
    case AfterDiffSearch:      ++(d_statistics.d_successAfterDiffSearch); break;
    case DuringVarOrderSearch: ++(d_statistics.d_successDuringVarOrderSearch); break;
    case AfterVarOrderSearch:  ++(d_statistics.d_successAfterVarOrderSearch); break;
    }
    d_successes.purge();
    return true;
  }else{
    return false;
  }
}

Result::Sat SimplexDecisionProcedure::dualFindModel(bool exactResult){
  Assert(d_conflictVariable == ARITHVAR_SENTINEL);
  Assert(d_queue.inCollectionMode());

  if(d_queue.empty()){
    return Result::SAT;
  }
  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;
  Debug("arith::findModel") << "begin findModel()" << instance << endl;

  d_queue.transitionToDifferenceMode();

  Result::Sat result = Result::SAT_UNKNOWN;

  if(d_queue.empty()){
    result = Result::SAT;
  }else if(d_queue.size() > 1){
    if(findConflictOnTheQueue(BeforeDiffSearch)){
      result = Result::UNSAT;
    }
  }
  static const bool verbose = false;
  exactResult |= options::arithStandardCheckVarOrderPivots() < 0;
  const uint32_t inexactResultsVarOrderPivots = exactResult ? 0 : options::arithStandardCheckVarOrderPivots();

  uint32_t checkPeriod = options::arithSimplexCheckPeriod();
  if(result == Result::SAT_UNKNOWN){
    uint32_t numDifferencePivots = options::arithHeuristicPivots() < 0 ?
      d_numVariables + 1 : options::arithHeuristicPivots();
    // The signed to unsigned conversion is safe.
    uint32_t pivotsRemaining = numDifferencePivots;
    while(!d_queue.empty() &&
          result != Result::UNSAT &&
          pivotsRemaining > 0){
      uint32_t pivotsToDo = min(checkPeriod, pivotsRemaining);
      pivotsRemaining -= pivotsToDo;
      if(searchForFeasibleSolution(pivotsToDo)){
        result = Result::UNSAT;
      }//Once every CHECK_PERIOD examine the entire queue for conflicts
      if(result != Result::UNSAT){
        if(findConflictOnTheQueue(DuringDiffSearch)) { result = Result::UNSAT; }
      }else{
        findConflictOnTheQueue(AfterDiffSearch); // already unsat
      }
    }

    if(verbose && numDifferencePivots > 0){
      if(result ==  Result::UNSAT){
        Message() << "diff order found unsat" << endl;
      }else if(d_queue.empty()){
        Message() << "diff order found model" << endl;
      }else{
        Message() << "diff order missed" << endl;
      }
    }
  }

  if(!d_queue.empty() && result != Result::UNSAT){
    if(exactResult){
      d_queue.transitionToVariableOrderMode();

      while(!d_queue.empty() && result != Result::UNSAT){
        if(searchForFeasibleSolution(checkPeriod)){
          result = Result::UNSAT;
        }

        //Once every CHECK_PERIOD examine the entire queue for conflicts
        if(result != Result::UNSAT){
          if(findConflictOnTheQueue(DuringVarOrderSearch)){
            result = Result::UNSAT;
          }
        } else{
          findConflictOnTheQueue(AfterVarOrderSearch);
        }
      }
      if(verbose){
        if(result ==  Result::UNSAT){
          Message() << "bland found unsat" << endl;
        }else if(d_queue.empty()){
          Message() << "bland found model" << endl;
        }else{
          Message() << "bland order missed" << endl;
        }
      }
    }else{
      d_queue.transitionToVariableOrderMode();

      if(searchForFeasibleSolution(inexactResultsVarOrderPivots)){
        result = Result::UNSAT;
        findConflictOnTheQueue(AfterVarOrderSearch); // already unsat
      }else{
        if(findConflictOnTheQueue(AfterVarOrderSearch)) { result = Result::UNSAT; }
      }

      if(verbose){
        if(result ==  Result::UNSAT){
          Message() << "restricted var order found unsat" << endl;
        }else if(d_queue.empty()){
          Message() << "restricted var order found model" << endl;
        }else{
          Message() << "restricted var order missed" << endl;
        }
      }
    }
  }

  if(result == Result::SAT_UNKNOWN && d_queue.empty()){
    result = Result::SAT;
  }



  d_pivotsInRound.purge();
  // ensure that the conflict variable is still in the queue.
  if(d_conflictVariable != ARITHVAR_SENTINEL){
    d_queue.enqueueIfInconsistent(d_conflictVariable);
  }
  d_conflictVariable = ARITHVAR_SENTINEL;

  d_queue.transitionToCollectionMode();
  Assert(d_queue.inCollectionMode());
  Debug("arith::findModel") << "end findModel() " << instance << " " << result <<  endl;
  return result;


  // Assert(foundConflict || d_queue.empty());

  // // Curiously the invariant that we always do a full check
  // // means that the assignment we can always empty these queues.
  // d_queue.clear();
  // d_pivotsInRound.purge();
  // d_conflictVariable = ARITHVAR_SENTINEL;

  // Assert(!d_queue.inCollectionMode());
  // d_queue.transitionToCollectionMode();


  // Assert(d_queue.inCollectionMode());

  // Debug("arith::findModel") << "end findModel() " << instance << endl;

  // return foundConflict;
}



Node SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic){

  Assert(d_tableau.isBasic(basic));
  const DeltaRational& beta = d_partialModel.getAssignment(basic);

  if(d_partialModel.strictlyLessThanLowerBound(basic, beta)){
    ArithVar x_j = selectSlackUpperBound(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictBelowLowerBound(basic);
    }
  }else if(d_partialModel.strictlyGreaterThanUpperBound(basic, beta)){
    ArithVar x_j = selectSlackLowerBound(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictAboveUpperBound(basic);
    }
  }
  return Node::null();
}

//corresponds to Check() in dM06
//template <SimplexDecisionProcedure::PreferenceFunction pf>
bool SimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  Debug("arith") << "searchForFeasibleSolution" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0){
    if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }

    ArithVar x_i = d_queue.dequeueInconsistentBasicVariable();
    Debug("arith::update::select") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Debug("arith_update") << "No inconsistent variables" << endl;
      return false; //sat
    }

    --remainingIterations;

    bool useVarOrderPivot = d_pivotsInRound.count(x_i) >=  options::arithPivotThreshold();
    if(!useVarOrderPivot){
      d_pivotsInRound.add(x_i);
    }


    Debug("playground") << "pivots in rounds: " <<  d_pivotsInRound.count(x_i)
                        << " use " << useVarOrderPivot
                        << " threshold " << options::arithPivotThreshold()
                        << endl;

    PreferenceFunction pf = useVarOrderPivot ? minVarOrder : minBoundAndRowCount;

    DeltaRational beta_i = d_partialModel.getAssignment(x_i);
    ArithVar x_j = ARITHVAR_SENTINEL;

    if(d_partialModel.strictlyLessThanLowerBound(x_i, beta_i)){
      x_j = selectSlackUpperBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        Node conflict = generateConflictBelowLowerBound(x_i); //unsat
        d_conflictVariable = x_i;
        reportConflict(conflict);
        return true;
      }
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      d_linEq.pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_partialModel.strictlyGreaterThanUpperBound(x_i, beta_i)){
      x_j = selectSlackLowerBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        Node conflict = generateConflictAboveUpperBound(x_i); //unsat

        d_conflictVariable = x_i;
        reportConflict(conflict);
        return true;
      }
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      d_linEq.pivotAndUpdate(x_i, x_j, u_i);
    }
    Assert(x_j != ARITHVAR_SENTINEL);

    //Check to see if we already have a conflict with x_j to prevent wasteful work
    if(CHECK_AFTER_PIVOT){
      Node possibleConflict = checkBasicForConflict(x_j);
      if(!possibleConflict.isNull()){
        d_conflictVariable = x_j;
        reportConflict(possibleConflict);
        return true; // unsat
      }
    }
  }
  Assert(remainingIterations == 0);

  return false;
}



Constraint SimplexDecisionProcedure::weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v, const Rational& coeff, bool& anyWeakening, ArithVar basic){

  int sgn = coeff.sgn();
  bool ub = aboveUpper?(sgn < 0) : (sgn > 0);

  Constraint c = ub ?
    d_partialModel.getUpperBoundConstraint(v) :
    d_partialModel.getLowerBoundConstraint(v);

// #warning "revisit"
//   Node exp = ub ?
//     d_partialModel.explainUpperBound(v) :
//     d_partialModel.explainLowerBound(v);

  bool weakened;
  do{
    const DeltaRational& bound = c->getValue();

    weakened = false;

    Constraint weaker = ub?
      c->getStrictlyWeakerUpperBound(true, true):
      c->getStrictlyWeakerLowerBound(true, true);

    // Node weaker = ub?
    //   d_propManager.strictlyWeakerAssertedUpperBound(v, bound):
    //   d_propManager.strictlyWeakerAssertedLowerBound(v, bound);

    if(weaker != NullConstraint){
    //if(!weaker.isNull()){
      const DeltaRational& weakerBound = weaker->getValue();
      //DeltaRational weakerBound = asDeltaRational(weaker);

      DeltaRational diff = aboveUpper ? bound - weakerBound : weakerBound - bound;
      //if var == basic,
      //  if aboveUpper, weakerBound > bound, multiply by -1
      //  if !aboveUpper, weakerBound < bound, multiply by -1
      diff = diff * coeff;
      if(surplus > diff){
        ++d_statistics.d_weakenings;
        weakened = true;
        anyWeakening = true;
        surplus = surplus - diff;

        Debug("weak") << "found:" << endl;
        if(v == basic){
          Debug("weak") << "  basic: ";
        }
        Debug("weak") << "  " << surplus << " "<< diff  << endl
                      << "  " << bound << c << endl
                      << "  " << weakerBound << weaker << endl;

        Assert(diff > d_DELTA_ZERO);
        c = weaker;
      }
    }
  }while(weakened);

  return c;
}

Node SimplexDecisionProcedure::weakenConflict(bool aboveUpper, ArithVar basicVar){
  TimerStat::CodeTimer codeTimer(d_statistics.d_weakenTime);

  const DeltaRational& assignment = d_partialModel.getAssignment(basicVar);
  DeltaRational surplus;
  if(aboveUpper){
    Assert(d_partialModel.hasUpperBound(basicVar));
    Assert(assignment > d_partialModel.getUpperBound(basicVar));
    surplus = assignment - d_partialModel.getUpperBound(basicVar);
  }else{
    Assert(d_partialModel.hasLowerBound(basicVar));
    Assert(assignment < d_partialModel.getLowerBound(basicVar));
    surplus = d_partialModel.getLowerBound(basicVar) - assignment;
  }

  NodeBuilder<> conflict(kind::AND);
  bool anyWeakenings = false;
  for(Tableau::RowIterator i = d_tableau.basicRowIterator(basicVar); !i.atEnd(); ++i){
    const Tableau::Entry& entry = *i;
    ArithVar v = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    bool weakening = false;
    Constraint c = weakestExplanation(aboveUpper, surplus, v, coeff, weakening, basicVar);
    Debug("weak") << "weak : " << weakening << " "
                  << c->assertedToTheTheory() << " "
                  << d_partialModel.getAssignment(v) << " "
                  << c << endl
                  << c->explainForConflict() << endl;
    anyWeakenings = anyWeakenings || weakening;

    Debug("weak") << "weak : " << c->explainForConflict() << endl;
    c->explainForConflict(conflict);
  }
  ++d_statistics.d_weakeningAttempts;
  if(anyWeakenings){
    ++d_statistics.d_weakeningSuccesses;
  }
  return conflict;
}


Node SimplexDecisionProcedure::generateConflictAboveUpperBound(ArithVar conflictVar){
  return weakenConflict(true, conflictVar);
}

Node SimplexDecisionProcedure::generateConflictBelowLowerBound(ArithVar conflictVar){
  return weakenConflict(false, conflictVar);
}


// responses 
//   unbounded below(arithvar)
//   reached threshold
//   reached maxpivots
//   reached GlobalMinimumd
//   
SimplexDecisionProcedure::PrimalResponse SimplexDecisionProcedure::primal(uint32_t maxIterations)
{
  Assert(d_optRow != ARITHVAR_SENTINEL);

  for(uint32_t iteration = 0; iteration < maxIterations; iteration++){
    if(belowThreshold()){
      return ReachedThresholdValue;
    }

    PrimalResponse res = primalCheck();
    switch(res){
    case GlobalMinimum:
    case FoundUnboundedVariable:
      return res;
    case NoProgressOnLeaving:
      ++d_statistics.d_primalPivots;
      ++d_pivotsSinceOptProgress;
      ++d_pivotsSinceLastCheck;
      ++d_pivotsSinceErrorProgress;

      d_linEq.pivotAndUpdate(d_primalCarry.d_entering, d_primalCarry.d_leaving, d_partialModel.getAssignment(d_primalCarry.d_entering));

      if(Debug.isOn("primal::tableau")){
	d_linEq.debugCheckTableau();
      }
      if(Debug.isOn("primal::consistent")){ Assert(d_linEq.debugEntireLinEqIsConsistent("MakeProgressOnLeaving")); }

      break;
    case MakeProgressOnLeaving:
      {
	++d_statistics.d_primalPivots;
	++d_statistics.d_primalImprovingPivots;

	d_pivotsSinceOptProgress = 0;
	++d_pivotsSinceErrorProgress;
	++d_pivotsSinceLastCheck;

	d_linEq.pivotAndUpdate(d_primalCarry.d_entering, d_primalCarry.d_leaving, d_primalCarry.d_nextEnteringValue);

	static int helpful = 0;
	static int hurtful = 0;
	static int penguin = 0;
	if(d_currentErrorVariables.isKey(d_primalCarry.d_entering)){
	  cout << "entering is error " << d_primalCarry.d_entering;
	  if(d_currentErrorVariables[d_primalCarry.d_entering].errorIsLeqZero(d_partialModel)){
	    cout << " now below threshold (" << (++helpful) << ") " << d_pivotsSinceErrorProgress << endl;
	  }else{
	    cout << "ouch (" << (++hurtful) << ")"<< d_pivotsSinceErrorProgress << endl;
	  }
	}else if(d_currentErrorVariables.isKey(d_primalCarry.d_leaving)){
	  cout << "leaving is error " << d_primalCarry.d_leaving;
	  if(d_currentErrorVariables[d_primalCarry.d_leaving].errorIsLeqZero(d_partialModel)){
	    cout << " now below threshold(" << (++helpful) << ")" << d_pivotsSinceErrorProgress << endl;
	  }else{
	    cout << "ouch (" << (++hurtful) << ")" << d_pivotsSinceErrorProgress<< endl;
	  }
	}else{
	  cout << " penguin (" << (++penguin) << ")" << d_pivotsSinceErrorProgress<< endl;
	}

	if(Debug.isOn("primal::tableau")){
	  d_linEq.debugCheckTableau();
	}
	if(Debug.isOn("primal::consistent")){ Assert(d_linEq.debugEntireLinEqIsConsistent("MakeProgressOnLeaving")); }
      }
      break;
    default:
      Unreachable();
    }
  }
  return UsedMaxPivots;
}


/**
 * Error set
 * ErrorVariable |-> {ErrorVariable, InputVariable, InputConstraint}
 */

/**
 * Returns SAT if it was able to satisfy all of the constraints in the error set
 * Returns UNSAT if it was able to able to find an error 
 */
Result::Sat SimplexDecisionProcedure::primalConverge(int depth){
  d_pivotsSinceLastCheck = 0;

  while(!d_currentErrorVariables.empty()){
    PrimalResponse res = primal(MAX_ITERATIONS - d_pivotsSinceLastCheck);

    switch(res){
    case FoundUnboundedVariable:

      // Drive the variable to at least 0
      // TODO This variable should be driven to a value that makes all of the error functions including it 0
      // It'll or another unbounded will be selected in the next round anyways so ignore for now.
      ++d_statistics.d_unboundedFound;
      if( !belowThreshold() ){
	driveOptToZero(d_primalCarry.d_unbounded);
	d_linEq.debugCheckTableau();
	if(Debug.isOn("primal::consistent")){ Assert(d_linEq.debugEntireLinEqIsConsistent("primalConverge")); }

	++d_statistics.d_unboundedFound_drive;
      }
      Assert(belowThreshold());
      {      
	uint32_t dropped = contractErrorVariables(true);
	Debug("primal::converge") << "primalConverge -> FoundUnboundedVariable -> dropped " << dropped  << " to " << d_currentErrorVariables.size() << endl;
	d_statistics.d_unboundedFound_dropped += dropped;
      }
      break;
    case ReachedThresholdValue:
      ++d_statistics.d_primalThresholdReachedPivot;

      Assert(belowThreshold());
      {
	uint32_t dropped = contractErrorVariables(true);
	Debug("primal::converge") << "primalConverge -> ReachedThresholdValue -> dropped " << dropped  << " to " << d_currentErrorVariables.size() << endl;
	d_statistics.d_primalThresholdReachedPivot_dropped += dropped;
      }
      break;
    case UsedMaxPivots:
      {
	d_pivotsSinceLastCheck = 0;
	++d_statistics.d_primalReachedMaxPivots;

	// periodically attempt to do the following : 
	//   contract the error variable
	//   check for a conflict on an error variable
	uint32_t dropped = contractErrorVariables(false);
	
	if( checkForRowConflicts() ){ // try to periodically look for a row 
	  Debug("primal::converge") << "primalConverge -> UsedMaxPivots -> unsat " << endl;

	  ++d_statistics.d_primalReachedMaxPivots_checkForConflictWorked;
	  return Result::UNSAT; // row conflicts are minimal so stop.
	}

	if(dropped > 0){
	  Debug("primal::converge") << "primalConverge -> UsedMaxPivots -> dropped " << dropped  << " to " << d_currentErrorVariables.size() << endl;
	  ++d_statistics.d_primalReachedMaxPivots_contractMadeProgress;
	}else{
	  Debug("primal::converge") << "primalConverge -> UsedMaxPivots -> nothing " << endl;
	}
      }
      break;
    case GlobalMinimum:
      ++d_statistics.d_primalGlobalMinimum;

      // If the minimum is positive, this is unsat.
      // However, the optimization row is not necessarily a minimal conflict
      if(!belowThreshold()){

	if(d_currentErrorVariables.size() == 1){
	  // The optimization function is exactly the same as the last remaining variable
	  // The conflict for the row is the same as the conflict for the optimization function.
	  bool foundConflict = checkForRowConflicts();
	  Assert(foundConflict);
	  Debug("primal::converge") << "primalConverge -> GlobalMinimum -> one variable" << endl;

	  return Result::UNSAT;
	}else{
	  // There are at least 2 error variables.
	  // Look for a minimal conflict


	  if(checkForRowConflicts() ){
	    Debug("primal::converge") << "primalConverge -> GlobalMinimum -> postitive -> rowconflict " << endl;
		  
	    ++d_statistics.d_primalGlobalMinimum_rowConflictWorked;
	    return Result::UNSAT;
	  }

	  uint32_t dropped = contractErrorVariables(false);
	  
	  Debug("primal::converge") << "primalConverge -> GlobalMinimum -> postitive -> dropped " << dropped  << " to " << d_currentErrorVariables.size() << endl;
	  if(dropped > 0){
	    ++d_statistics.d_primalGlobalMinimum_contractMadeProgress;
	  }

	  ErrorMap half;
	  d_currentErrorVariables.splitInto(half);

	  Debug("primal::converge") << "primalConverge -> GlobalMinimum -> recursion " << depth << endl;


	  reconstructOptimizationFunction();
	  Result::Sat resultOnRemaining = primalConverge(depth + 1);

	  if(resultOnRemaining == Result::UNSAT){
	    Debug("primal::converge") << "primalConverge -> GlobalMinimum -> recursion " << depth << " was unsat " << endl;
	    ++d_statistics.d_primalGlobalMinimum_firstHalfWasUnsat;
	    restoreErrorVariables(half);
	    return Result::UNSAT;
	  }else{
	    ++d_statistics.d_primalGlobalMinimum_firstHalfWasSat;
	    Debug("primal::converge") << "primalConverge -> GlobalMinimum -> recursion " << depth << " was sat " << endl;

	    Assert(resultOnRemaining == Result::SAT);
	    Assert(d_currentErrorVariables.empty());
	    d_currentErrorVariables.addAll(half);
	    reconstructOptimizationFunction();
	    return primalConverge(depth + 1);
	  }
	}

      }else{

	// if the optimum is <= 0
	// drop all of the satisfied variables and continue;
	uint32_t dropped = contractErrorVariables(true);
	Debug("primal::converge") << "primalConverge -> GlobalMinimum -> negative -> dropped "<< dropped  << " to " << d_currentErrorVariables.size() << endl;

	++d_statistics.d_primalGlobalMinimum_contractMadeProgress;
      }
      break;
    default:
      Unreachable();
    }
   }

   return Result::SAT;
}


Result::Sat SimplexDecisionProcedure::primalFindModel(){
  Assert(d_primalCarry.isClear());

  // Reduce the queue to only contain violations
  reduceQueue();

  if(d_queue.empty()){
    return Result::SAT;
  }
  TimerStat::CodeTimer codeTimer(d_statistics.d_primalTimer);
  
  ++d_statistics.d_primalCalls;

  Debug("primalFindModel") << "primalFindModel() begin" << endl;

  const int PAUSE_RATE = 100;
  if(Debug.isOn("primal::pause") && d_statistics.d_primalCalls.getData() % PAUSE_RATE  == 0){
    Debug("primal::pause") << "waiting for input: ";
    std::string dummy;
    std::getline(std::cin, dummy);
  }

  // TODO restore the tableau by ejecting variables
  //  Tableau copy(d_tableau);

  Result::Sat answer;
  {
    TimerStat::CodeTimer codeTimer(d_statistics.d_internalTimer);

    // This is needed because of the fiddling with the partial model
    //context::Context::ScopedPush speculativePush(satContext);

    constructErrorVariables();
    constructOptimizationFunction();
    if(Debug.isOn("primal::tableau")){ d_linEq.debugCheckTableau(); }
    if(Debug.isOn("primal::consistent")){ d_linEq.debugEntireLinEqIsConsistent("primalFindModel 1"); }
    answer = primalConverge(0);
  }
  removeOptimizationFunction();


  // exit
  uint32_t nc = d_tableau.getNumColumns();
  //d_tableau = copy;
  while(d_tableau.getNumColumns() < nc){
    d_tableau.increaseSize();
  }
  restoreErrorVariables(d_currentErrorVariables);

  reduceQueue();

  if(Debug.isOn("primal::tableau")){ d_linEq.debugCheckTableau(); }

  if(Debug.isOn("primal::consistent")){ d_linEq.debugEntireLinEqIsConsistent("primalFindModel2"); }
  Debug("primalFindModel") << "primalFindModel() end " << answer << endl;

  // The set of variables in conflict with their bounds will still be a subset of the
  // variables that are in conflict with their bounds in the beginning.
  // The basic variables are the same because of the copy.
  // Thus it is safe to not try to not recompute the queue of violating variables

  if(answer == Result::UNSAT){
    // This needs to be done in a different context level than the push
    ++d_statistics.d_primalUnsatCalls;
  }else{
    ++d_statistics.d_primalSatCalls;
  }
  
  d_primalCarry.clear();

  return answer;
}

/** Clears the ErrorMap and relase the resources associated with it.
 * There are a couple of error maps around
 */
void SimplexDecisionProcedure::restoreErrorVariables(SimplexDecisionProcedure::ErrorMap& es){
  while(!es.empty()){
    ArithVar e = es.back();

    reassertErrorConstraint(e, es, false, false);
    es.pop_back();
  }
}

void SimplexDecisionProcedure::constructErrorVariables(){
  Assert(d_currentErrorVariables.empty());
  Assert(!d_queue.empty());

  for(ArithPriorityQueue::const_iterator iter = d_queue.begin(), end = d_queue.end(); iter != end; ++iter){
    ArithVar input = *iter;

    Assert(d_tableau.isBasic(input));
    Assert(!d_partialModel.assignmentIsConsistent(input));

    Assert(!d_currentErrorVariables.isKey(input));

    bool ub = d_partialModel.strictlyGreaterThanUpperBound(input, d_partialModel.getAssignment(input));

    Constraint original =  ub ? d_partialModel.getUpperBoundConstraint(input)
      :  d_partialModel.getLowerBoundConstraint(input);

    d_currentErrorVariables.set(input, ErrorInfo(input, ub, original));

    if(ub){
      d_partialModel.forceRelaxUpperBound(input);
    }else{
      d_partialModel.forceRelaxLowerBound(input);
    }
    Debug("primal") << "adding error variable (" << input << ", " << ", " << original <<") ";
    Debug("primal") << "ub "<< ub << " " <<  d_partialModel.getAssignment(input)  << " " <<  original->getValue() <<")" << endl;
    d_currentErrorVariables.set(input, ErrorInfo(input, ub, original));

    // Constraint boundIsValue = d_constraintDatabase.getConstraint(bound, Equality, original->getValue());
    // boundIsValue->setPsuedoConstraint();

    // d_partialModel.setAssignment(bound, boundIsValue->getValue());
    // d_partialModel.setUpperBoundConstraint(boundIsValue);
    // d_partialModel.setLowerBoundConstraint(boundIsValue);

    // // if ub
    // // then  error = x - boundIsValue
    // // else  error = boundIsValue - x

    // ArithVar error = requestVariable();

    // DeltaRational diff = ub ?
    //   d_partialModel.getAssignment(input) - boundIsValue->getValue() :
    //   boundIsValue->getValue() - d_partialModel.getAssignment(input);

    // d_partialModel.setAssignment(error, diff);

    // vector<Rational> coeffs;
    // vector<ArithVar> variables;
    // variables.push_back(input);
    // coeffs.push_back(ub ? Rational(1) : Rational(-1));
    // variables.push_back(bound);
    // coeffs.push_back(ub ? Rational(-1) : Rational(1));

    // d_tableau.addRow(error, coeffs, variables);


  }

  if(Debug.isOn("primal::tableau")){ d_linEq.debugCheckTableau(); }
  if(Debug.isOn("primal::consistent")){  d_linEq.debugEntireLinEqIsConsistent("constructErrorVariables");}
  Assert(!d_currentErrorVariables.empty());
}



/** Returns true if it has found a row conflict for any of the error variables. */
bool SimplexDecisionProcedure::checkForRowConflicts(){
  vector<ArithVar> inConflict;
  for(ErrorMap::const_iterator iter = d_currentErrorVariables.begin(), end = d_currentErrorVariables.end(); iter != end; ++iter){
    ArithVar error = *iter;
    const ErrorInfo& info = d_currentErrorVariables[error];
    if(d_tableau.isBasic(error) && !info.errorIsLeqZero(d_partialModel)){

      ArithVar x_j = info.isUpperbound() ?
	selectSlackLowerBound(error) :
	selectSlackUpperBound(error);

      if(x_j == ARITHVAR_SENTINEL ){
	inConflict.push_back(error);
      }
    }
  }

  if(!inConflict.empty()){
    while(!inConflict.empty()){
      ArithVar error = inConflict.back();
      inConflict.pop_back();

      reassertErrorConstraint(error, d_currentErrorVariables, false, true);

      Node conflict =  d_currentErrorVariables[error].isUpperbound() ?
	generateConflictAboveUpperBound(error) :
	generateConflictBelowLowerBound(error);
      Assert(!conflict.isNull());

      d_currentErrorVariables.remove(error);
      
      reportConflict(conflict);
    }
    reconstructOptimizationFunction();
    return true;
  }else{
    return false;
  }
}

void SimplexDecisionProcedure::reassertErrorConstraint(ArithVar e, SimplexDecisionProcedure::ErrorMap& es, bool definitelyTrue, bool definitelyFalse){
  Assert(es.isKey(e));
  const ErrorInfo& info = es.get(e);
  Constraint original = info.getConstraint();

  if(info.isUpperbound()){
    d_partialModel.setUpperBoundConstraint(original);
  }else if(original->isLowerBound()){
    d_partialModel.setLowerBoundConstraint(original);
  }

  Assert(!definitelyTrue || d_partialModel.assignmentIsConsistent(e));
  Assert(!definitelyFalse || !d_partialModel.assignmentIsConsistent(e));
}

uint32_t SimplexDecisionProcedure::contractErrorVariables(bool guaranteedSuccess){
  uint32_t entrySize = d_currentErrorVariables.size();
  Debug("primal::contract") << "contractErrorVariables() begin : " << d_currentErrorVariables.size() << endl;

  std::vector<ArithVar> toRemove;
  for(ErrorMap::const_iterator iter = d_currentErrorVariables.begin(), end = d_currentErrorVariables.end(); iter != end; ++iter){
    ArithVar e = *iter;
    if(d_currentErrorVariables[e].errorIsLeqZero(d_partialModel)){
      toRemove.push_back(e);
    }
  }

  Assert(!guaranteedSuccess || !toRemove.empty());

  if(!toRemove.empty()){
    while(!toRemove.empty()){
      ArithVar e = toRemove.back();
      toRemove.pop_back();
      reassertErrorConstraint(e, d_currentErrorVariables, true, false);
      d_currentErrorVariables.remove(e);
    }

    reconstructOptimizationFunction();
  }    

  Debug("primal::contract") << "contractErrorVariables() end : " << d_currentErrorVariables.size() << endl;
  
  uint32_t exitSize = d_currentErrorVariables.size();

  Assert(exitSize <= entrySize);
  Assert(!guaranteedSuccess|| exitSize < entrySize);
  return entrySize - exitSize;
}

void SimplexDecisionProcedure::removeOptimizationFunction(){
  Assert(d_optRow != ARITHVAR_SENTINEL);
  Assert(d_tableau.isBasic(d_optRow));
  
  d_tableau.removeBasicRow(d_optRow);
  releaseVariable(d_optRow);

  d_optRow = ARITHVAR_SENTINEL;
  d_negOptConstant = d_DELTA_ZERO;

  Assert(d_optRow == ARITHVAR_SENTINEL);
}

void SimplexDecisionProcedure::constructOptimizationFunction(){
  Assert(d_optRow == ARITHVAR_SENTINEL);
  Assert(d_negOptConstant == d_DELTA_ZERO);
  
  d_optRow = requestVariable();


  std::vector<Rational> coeffs;
  std::vector<ArithVar> variables;
  for(ErrorMap::const_iterator iter = d_currentErrorVariables.begin(), end = d_currentErrorVariables.end(); iter != end; ++iter){
    ArithVar e = *iter;

    if(d_currentErrorVariables[e].isUpperbound()){
      coeffs.push_back(Rational(1)); 
      variables.push_back(e);
      d_negOptConstant = d_negOptConstant + (d_currentErrorVariables[e].getConstraint()->getValue());
    }else{
      coeffs.push_back(Rational(-1));
      variables.push_back(e);
      d_negOptConstant = d_negOptConstant - (d_currentErrorVariables[e].getConstraint()->getValue());
    }
  }
  d_tableau.addRow(d_optRow, coeffs, variables);

  DeltaRational newAssignment = d_linEq.computeRowValue(d_optRow, false);
  d_partialModel.setAssignment(d_optRow, newAssignment);

  if(Debug.isOn("primal::tableau")){ d_linEq.debugCheckTableau(); }


  if(Debug.isOn("primal::consistent")){
    d_linEq.debugEntireLinEqIsConsistent("constructOptimizationFunction");
  }

  d_pivotsSinceOptProgress = 0;
  d_pivotsSinceErrorProgress = 0;

  Assert(d_optRow != ARITHVAR_SENTINEL);
}

void SimplexDecisionProcedure::reconstructOptimizationFunction(){
  removeOptimizationFunction();
  constructOptimizationFunction();
}



/* TODO:
 * Very naive implementation. Recomputes everything every time.
 * Currently looks for the variable that can decrease the optimization function the most.
 * 
 */
SimplexDecisionProcedure::PrimalResponse SimplexDecisionProcedure::primalCheck()
{
  Debug("primal") << "primalCheck() begin" << endl;

  ArithVar leaving = ARITHVAR_SENTINEL;
  ArithVar entering =  ARITHVAR_SENTINEL;
  DeltaRational leavingShift = d_DELTA_ZERO; // The amount the leaving variable can change by without making the tableau inconsistent
  DeltaRational leavingDelta = d_DELTA_ZERO; // The amount the optimization function changes by selecting leaving
  
  Assert(d_improvementCandidates.empty());

  for( Tableau::RowIterator ri = d_tableau.basicRowIterator(d_optRow); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;

    ArithVar curr = e.getColVar();
    if(curr == d_optRow){ continue; }


    int sgn = e.getCoefficient().sgn();
    Assert(sgn != 0);
    if( (sgn < 0 && d_partialModel.strictlyBelowUpperBound(curr)) ||
	(sgn > 0 && d_partialModel.strictlyAboveLowerBound(curr)) ){

      d_improvementCandidates.push_back(&e);
    }
  }

  if(d_improvementCandidates.empty()){
    Debug("primal") << "primalCheck() end : global" << endl;
    return GlobalMinimum; // No variable in the optimization function can be improved
  }
  
  DeltaRational minimumShift;
  DeltaRational currShift;
  for(EntryVector::const_iterator ci = d_improvementCandidates.begin(), end_ci = d_improvementCandidates.end(); ci != end_ci; ++ci){
    const Tableau::Entry& e = *(*ci);
    ArithVar curr = e.getColVar();

    ArithVar currEntering;
    bool progress;
    
    minimumShift = (leaving == ARITHVAR_SENTINEL ) ? leavingDelta/(e.getCoefficient().abs()) : d_DELTA_ZERO;
    int sgn = e.getCoefficient().sgn();
    computeShift(curr, sgn < 0, progress, currEntering, currShift, minimumShift);

    if(currEntering == ARITHVAR_SENTINEL){
      d_improvementCandidates.clear();

      Debug("primal") << "primalCheck() end : unbounded" << endl;
      d_primalCarry.d_unbounded = curr;
      return FoundUnboundedVariable;
    }else if(progress) {
      leaving = curr;
      leavingShift = currShift;
      leavingDelta = currShift * e.getCoefficient();
      entering = currEntering;

      Assert(leavingDelta < d_DELTA_ZERO);

      const int RECHECK_PERIOD = 10;
      if(d_pivotsSinceErrorProgress % RECHECK_PERIOD != 0){
	// we can make progress, stop
	break;
      }
    }
  }

  if(leaving == ARITHVAR_SENTINEL){
    cout << "Nothing can make progress " << endl;

    const uint32_t THRESHOLD = 20;
    if(d_pivotsSinceOptProgress <= THRESHOLD){

      int index = rand() % d_improvementCandidates.size();
      leaving =  (*d_improvementCandidates[index]).getColVar();
      entering = selectFirstValid(leaving, (*d_improvementCandidates[index]).getCoefficient().sgn() < 0);
    }else{ // Bland's rule
      bool increasing;
      for(EntryVector::const_iterator ci = d_improvementCandidates.begin(), end_ci = d_improvementCandidates.end(); ci != end_ci; ++ci){
	const Tableau::Entry& e = *(*ci);
	ArithVar curr = e.getColVar();
	leaving = (leaving == ARITHVAR_SENTINEL) ? curr : minVarOrder(*this, curr, leaving);
	if(leaving == curr){
	  increasing = (e.getCoefficient().sgn() < 0);
	}
      }
      
      entering = selectMinimumValid(leaving, increasing);
    }
    Assert(leaving != ARITHVAR_SENTINEL);
    Assert(entering != ARITHVAR_SENTINEL);

    d_primalCarry.d_leaving = leaving;
    d_primalCarry.d_entering = entering;

    d_primalCarry.d_nextEnteringValue = d_partialModel.getAssignment(entering);

    Debug("primal") << "primalCheck() end : no progress made " <<  leaving << " to " << entering << " (" << d_pivotsSinceOptProgress << ")"<< endl;
    d_improvementCandidates.clear();
    return NoProgressOnLeaving;
  }else{
    const Tableau::Entry& enterLeavingEntry = d_tableau.findEntry(d_tableau.basicToRowIndex(entering), leaving);
    Assert(!enterLeavingEntry.blank());

    d_primalCarry.d_leaving = leaving;
    d_primalCarry.d_entering = entering;
    d_primalCarry.d_nextEnteringValue = d_partialModel.getAssignment(entering)
      + leavingShift * enterLeavingEntry.getCoefficient();

    Debug("primal") << "primalCheck() end : progress" << endl
		    << leaving << " to " << entering << " ~ "
		    << d_partialModel.getAssignment(leaving) << " ~ "  << leavingShift
		    << " ~ " << enterLeavingEntry.getCoefficient()
		    << " ~ " << d_primalCarry.d_nextEnteringValue << endl;

    d_improvementCandidates.clear();
    return MakeProgressOnLeaving;
  }

  //   anyProgress = true;

  //     DeltaRational currDelta = currShift * e.getCoefficient();

  //     int cmp = currDelta.cmp(leavingDelta);
      
  //     // Cases:
  //     // 1) No candidate yet, 
  //     // 2) there is a candidate with a strictly better update, or
  //     // 3) there is a candidate with the same update value that has a smaller value in the variable ordering.
  //     //
  //     // Case 3 covers Bland's rule.
  //     if(entering == ARITHVAR_SENTINEL || cmp < 0){
  // 	leaving = curr;
  //     }else if( cmp == 0 ){
  // 	leaving = minVarOrder(*this, curr, leaving);
  //     }

  //     if(leaving == curr){
  // 	leavingShift = currShift;
  // 	leavingDelta = currDelta;
  // 	entering = currEntering;
  //     }
  //   }
  // }

  // if(leaving == ARITHVAR_SENTINEL){
  //   Debug("primal") << "primalCheck() end : global" << endl;
  //   return GlobalMinimum; // No variable in the optimization function can be improved
  // }else{
  //   const Tableau::Entry& enterLeavingEntry = d_tableau.findEntry(d_tableau.basicToRowIndex(entering), leaving);
  //   Assert(!enterLeavingEntry.blank());

  //   d_primalCarry.d_leaving = leaving;
  //   d_primalCarry.d_entering = entering;
  //   d_primalCarry.d_nextEnteringValue = d_partialModel.getAssignment(entering)
  //     + leavingShift * enterLeavingEntry.getCoefficient();

  //   Debug("primal") << "primalCheck() end : progress" << endl
  // 		    << leaving << " to " << entering << " ~ "
  // 		    << d_partialModel.getAssignment(leaving) << " ~ "  << leavingShift
  // 		    << " ~ " << enterLeavingEntry.getCoefficient()
  // 		    << " ~ " << d_primalCarry.d_nextEnteringValue << endl;
  //   return MakeProgressOnLeaving;
  // }
}

ArithVar SimplexDecisionProcedure::selectMinimumValid(ArithVar v, bool increasing){
  ArithVar minimum = ARITHVAR_SENTINEL;
  for(Tableau::ColIterator colIter = d_tableau.colIterator(v);!colIter.atEnd(); ++colIter){
    const Tableau::Entry& e = *colIter;
    ArithVar basic = d_tableau.rowIndexToBasic(e.getRowIndex());
    if(basic == d_optRow) continue;

    
    int esgn = e.getCoefficient().sgn();
    bool basicInc = (increasing  == (esgn > 0));

    if(!(basicInc ? d_partialModel.strictlyBelowUpperBound(basic) :
	 d_partialModel.strictlyAboveLowerBound(basic))){
      if(minimum == ARITHVAR_SENTINEL){
	minimum = basic;
      }else{
	minimum = minVarOrder(*this, basic, minimum);
      }
    }
  }
  return minimum;
}

ArithVar SimplexDecisionProcedure::selectFirstValid(ArithVar v, bool increasing){
  ArithVar minimum = ARITHVAR_SENTINEL;

  for(Tableau::ColIterator colIter = d_tableau.colIterator(v);!colIter.atEnd(); ++colIter){
    const Tableau::Entry& e = *colIter;
    ArithVar basic = d_tableau.rowIndexToBasic(e.getRowIndex());
    if(basic == d_optRow) continue;

    int esgn = e.getCoefficient().sgn();
    bool basicInc = (increasing  == (esgn > 0));

    if(!(basicInc ? d_partialModel.strictlyBelowUpperBound(basic) :
	 d_partialModel.strictlyAboveLowerBound(basic))){
      if(minimum == ARITHVAR_SENTINEL){
	minimum = basic;
      }else{
	minimum = minRowLength(*this, basic, minimum);
      }
    }
  }
  return minimum;
}



void SimplexDecisionProcedure::computeShift(ArithVar leaving, bool increasing, bool& progress, ArithVar& entering, DeltaRational& shift, const DeltaRational& minimumShift){
  Assert(increasing ? (minimumShift >= d_DELTA_ZERO) : (minimumShift <= d_DELTA_ZERO) );

  static int instance = 0;
  Debug("primal") << "computeshift " << ++instance  << " " << leaving << endl;

  // The selection for the leaving variable
  entering = ARITHVAR_SENTINEL;

  // no progress is initially made
  progress = false;

  bool bounded = false;

  if(increasing ? d_partialModel.hasUpperBound(leaving) : d_partialModel.hasLowerBound(leaving)){
    const DeltaRational& assignment = d_partialModel.getAssignment(leaving);

    bounded = true;

    DeltaRational diff = increasing ? d_partialModel.getUpperBound(leaving) - assignment : d_partialModel.getLowerBound(leaving) - assignment;
    Assert(increasing ? diff.sgn() >=0 : diff.sgn() <= 0);
    if((increasing) ? (diff < minimumShift) : ( diff > minimumShift)){
      Assert(!progress);
      entering = leaving; // My my my, what an ugly hack
      return; // no progress is possible stop
    }
  }

  // shift has a meaningful value once entering has a meaningful value
  // if increasing,
  // then  shift > minimumShift >= 0
  // else  shift < minimumShift <= 0
  //
  // Maintain the following invariant:
  //
  // if increasing,
  //    if e_ij > 0, diff >= shift > minimumShift >= 0
  //    if e_ij < 0, diff >= shift > minimumShift >= 0
  // if !increasing,
  //    if e_ij > 0, diff <= shift < minimumShift <= 0
  //    if e_ij < 0, diff <= shift < minimumShift <= 0
  // if increasing == (e_ij > 0), diff = (d_partialModel.getUpperBound(basic) - d_partialModel.getAssignment(basic)) / e.getCoefficient()
  // if increasing != (e_ij > 0), diff = (d_partialModel.getLowerBound(basic) - d_partialModel.getAssignment(basic)) / e.getCoefficient()

  for(Tableau::ColIterator colIter = d_tableau.colIterator(leaving);!colIter.atEnd(); ++colIter){
    const Tableau::Entry& e = *colIter;
    
    ArithVar basic = d_tableau.rowIndexToBasic(e.getRowIndex());
    if(basic == d_optRow) continue;

    int esgn = e.getCoefficient().sgn();
    bool basicInc = (increasing  == (esgn > 0));
    // If both are true, increasing the variable entering increases the basic variable
    // If both are false, the entering variable is decreasing, but the coefficient is negative and the basic variable is increasing
    // If exactly one is false, the basic variable is decreasing.

    Debug("primal::shift") << basic << " " << d_partialModel.hasUpperBound(basic) << " "
			   << d_partialModel.hasLowerBound(basic) << " "
			   << e.getCoefficient() << endl;

    if( (basicInc && d_partialModel.hasUpperBound(basic))||
	(!basicInc && d_partialModel.hasLowerBound(basic))){

      if(!(basicInc ? d_partialModel.strictlyBelowUpperBound(basic) :
	   d_partialModel.strictlyAboveLowerBound(basic))){
	// diff == 0, as diff > minimumShift >= 0 or diff < minimumShift <= 0
	Assert(!progress);
	entering = basic;
	return;
      }else{
	DeltaRational diff = basicInc ?
	  (d_partialModel.getUpperBound(basic) - d_partialModel.getAssignment(basic)) / e.getCoefficient() :
	  (d_partialModel.getLowerBound(basic) - d_partialModel.getAssignment(basic)) / e.getCoefficient();

	if( entering == ARITHVAR_SENTINEL ){
	  if(increasing ? (diff <= minimumShift) : (diff >= minimumShift)){
	    Assert(!progress);
	    entering = basic;
	    return;
	  }else{
	    Assert(increasing ? (diff > minimumShift) : (diff < minimumShift));
	    shift = diff;
	    entering = basic;
	    bounded = true;
	  }
	}else{
	  if( increasing ? (diff < shift) : diff > shift){
	    // a new min for increasing
	    // a new max for decreasing

	    if(increasing ? (diff <= minimumShift) : (diff >= minimumShift)){
	      Assert(!progress);
	      entering = basic;
	      return;
	    }else{
	      Assert(increasing ? (diff > minimumShift) : (diff < minimumShift));
	      shift = diff;
	      entering = basic;
	    }
	  }
	}
      }
    }
  }
  
  if(!bounded){
    // A totally unbounded variable
    Assert(entering == ARITHVAR_SENTINEL);
    progress = true;
    return;
  }else if(entering == ARITHVAR_SENTINEL){
    // We have a variable that is bounded only by its maximum
    for(Tableau::ColIterator colIter = d_tableau.colIterator(leaving);!colIter.atEnd(); ++colIter){
      const Tableau::Entry& e = *colIter;
    
      ArithVar basic = d_tableau.rowIndexToBasic(e.getRowIndex());
      if(basic == d_optRow){
	continue;
      } else{
	entering = basic;
	break;
      }
    }
    Assert(entering != ARITHVAR_SENTINEL);
    
    Assert(increasing ? d_partialModel.hasUpperBound(leaving) : d_partialModel.hasLowerBound(leaving));

    const DeltaRational& assignment = d_partialModel.getAssignment(leaving);
    DeltaRational diff = increasing ? d_partialModel.getUpperBound(leaving) - assignment : d_partialModel.getLowerBound(leaving) - assignment;
    
    shift = diff;

    Assert(increasing ? shift.sgn() >=0 : shift.sgn() <= 0);
    Assert(increasing ? shift > minimumShift : shift < minimumShift);

    progress = true;
    return;
  }else{
    Assert(bounded);
    progress = true;

    if((increasing ? d_partialModel.hasUpperBound(leaving) : d_partialModel.hasLowerBound(leaving) )){
      Assert(entering != ARITHVAR_SENTINEL);
      const DeltaRational& assignment = d_partialModel.getAssignment(leaving);
      DeltaRational diff = increasing ? d_partialModel.getUpperBound(leaving) - assignment : d_partialModel.getLowerBound(leaving) - assignment;
      if((increasing) ? (diff < shift) : ( diff > shift)){
	shift = diff;
      }
    }

    Assert(increasing ? shift.sgn() >=0 : shift.sgn() <= 0);
    Assert(increasing ? shift > minimumShift : shift < minimumShift);
    return;
  }
  
  
	// if(! bounded ||
	//    (increasing && diff < shift) || // a new min for increasing
	//    (!increasing && diff > shift)){ // a new max for decreasing
	//   bounded = true;
	//   shift = diff;
	//   entering = basic;
	// }
      // }

      // if(notAtTheBound && !blandMode){
      // 	DeltaRational diff = basicInc ?
      // 	  (d_partialModel.getUpperBound(basic) - d_partialModel.getAssignment(basic)) / e.getCoefficient() :
      // 	  (d_partialModel.getLowerBound(basic) - d_partialModel.getAssignment(basic)) / e.getCoefficient();

      // 	if(! bounded ||
      // 	   (increasing && diff < shift) || // a new min for increasing
      // 	   (!increasing && diff > shift)){ // a new max for decreasing
      // 	  bounded = true;
      // 	  shift = diff;
      // 	  entering = basic;
      // 	}
      // }else if (!notAtTheBound) { // basic is already exactly at the bound
      // 	if(!blandMode){ // Enter into using Bland's rule
      // 	  blandMode = true;
      // 	  bounded = true;
      // 	  shift = d_DELTA_ZERO;
      // 	  entering = basic;
      // 	}else{
      // 	  entering = minVarOrder(*this, entering, basic); // Bland's rule.
      // 	}
      // }
     // else this basic variable cannot be violated by increasing/decreasing entering
  

   

  // if(!blandMode && (increasing ? d_partialModel.hasUpperBound(leaving) : d_partialModel.hasLowerBound(leaving) )){
  //   Assert(entering != ARITHVAR_SENTINEL);
  //   bounded = true;
  //   DeltaRational diff = increasing ? d_partialModel.getUpperBound(leaving) - assignment : d_partialModel.getLowerBound(leaving) - assignment;
  //   if((increasing) ? (diff < shift) : ( diff > shift)){
  //     shift = diff;
  //   }
  // }

  // Assert(increasing ? shift.sgn() >=0 : shift.sgn() <= 0);

  // return shift;
}


/**
 * Given an variable on the optimization row that can be used to decrease the value of the optimization function
 * arbitrarily and an optimization function that is strictly positive in the current model,
 * driveOptToZero updates the value of unbounded s.t. the value of d_opt is exactly 0.
 */
void SimplexDecisionProcedure::driveOptToZero(ArithVar unbounded){
  Assert(!belowThreshold());

  const Tableau::Entry& e = d_tableau.findEntry(d_tableau.basicToRowIndex(d_optRow), unbounded);
  Assert(!e.blank());

  DeltaRational theta = (d_negOptConstant-d_partialModel.getAssignment(d_optRow))/ (e.getCoefficient());
  Assert((e.getCoefficient().sgn() > 0) ? (theta.sgn() < 0) : (theta.sgn() > 0));

  DeltaRational newAssignment = d_partialModel.getAssignment(unbounded) + theta;
  d_linEq.update(unbounded, newAssignment);

  if(Debug.isOn("primal::consistent")){ Assert(d_linEq.debugEntireLinEqIsConsistent("driveOptToZero")); }

  Assert(belowThreshold());
}
