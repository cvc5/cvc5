/*********************                                                        */
/*! \file dual_simplex.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "theory/arith/dual_simplex.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/constraint.h"


using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

DualSimplexDecisionProcedure::DualSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
  , d_pivotsInRound()
  , d_statistics(d_pivots)
{ }

DualSimplexDecisionProcedure::Statistics::Statistics(uint32_t& pivots):
  d_statUpdateConflicts("theory::arith::dual::UpdateConflicts", 0),
  d_processSignalsTime("theory::arith::dual::findConflictOnTheQueueTime"),
  d_simplexConflicts("theory::arith::dual::simplexConflicts",0),
  d_recentViolationCatches("theory::arith::dual::recentViolationCatches",0),
  d_searchTime("theory::arith::dual::searchTime"),
  d_finalCheckPivotCounter("theory::arith::dual::lastPivots", pivots)
{
  smtStatisticsRegistry()->registerStat(&d_statUpdateConflicts);
  smtStatisticsRegistry()->registerStat(&d_processSignalsTime);
  smtStatisticsRegistry()->registerStat(&d_simplexConflicts);
  smtStatisticsRegistry()->registerStat(&d_recentViolationCatches);
  smtStatisticsRegistry()->registerStat(&d_searchTime);
  smtStatisticsRegistry()->registerStat(&d_finalCheckPivotCounter);
}

DualSimplexDecisionProcedure::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_statUpdateConflicts);
  smtStatisticsRegistry()->unregisterStat(&d_processSignalsTime);
  smtStatisticsRegistry()->unregisterStat(&d_simplexConflicts);
  smtStatisticsRegistry()->unregisterStat(&d_recentViolationCatches);
  smtStatisticsRegistry()->unregisterStat(&d_searchTime);
  smtStatisticsRegistry()->unregisterStat(&d_finalCheckPivotCounter);
}

Result::Sat DualSimplexDecisionProcedure::dualFindModel(bool exactResult){
  Assert(d_conflictVariables.empty());

  static thread_local unsigned int instance = 0;
  instance = instance + 1;
  d_pivots = 0;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Debug("arith::findModel") << "dualFindModel("<< instance <<") trivial" << endl;
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);

  if(processSignals()){
    d_conflictVariables.purge();

    Debug("arith::findModel") << "dualFindModel("<< instance <<") early conflict" << endl;
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Debug("arith::findModel") << "dualFindModel("<< instance <<") fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    return Result::SAT;
  }

  Debug("arith::findModel") << "dualFindModel(" << instance <<") start non-trivial" << endl;

  Result::Sat result = Result::SAT_UNKNOWN;

  static const bool verbose = false;
  exactResult |= options::arithStandardCheckVarOrderPivots() < 0;


  uint32_t checkPeriod = options::arithSimplexCheckPeriod();
  if(result == Result::SAT_UNKNOWN){
    uint32_t numDifferencePivots = options::arithHeuristicPivots() < 0 ?
      d_numVariables + 1 : options::arithHeuristicPivots();
    // The signed to unsigned conversion is safe.
    if(numDifferencePivots > 0){

      d_errorSet.setSelectionRule(d_heuristicRule);
      if(searchForFeasibleSolution(numDifferencePivots)){
        result = Result::UNSAT;
      }
    }

    if(verbose && numDifferencePivots > 0){
      if(result ==  Result::UNSAT){
        Message() << "diff order found unsat" << endl;
      }else if(d_errorSet.errorEmpty()){
        Message() << "diff order found model" << endl;
      }else{
        Message() << "diff order missed" << endl;
      }
    }
  }
  Assert(!d_errorSet.moreSignals());

  if(!d_errorSet.errorEmpty() && result != Result::UNSAT){
    if(exactResult){
      d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);
      while(!d_errorSet.errorEmpty() && result != Result::UNSAT){
        Assert(checkPeriod > 0);
        if(searchForFeasibleSolution(checkPeriod)){
          result = Result::UNSAT;
        }
      }
    }else if( options::arithStandardCheckVarOrderPivots() > 0){
      d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);
      if(searchForFeasibleSolution(options::arithStandardCheckVarOrderPivots())){
        result = Result::UNSAT;
      }
      if(verbose){
        if(result ==  Result::UNSAT){
          Message() << "restricted var order found unsat" << endl;
        }else if(d_errorSet.errorEmpty()){
          Message() << "restricted var order found model" << endl;
        }else{
          Message() << "restricted var order missed" << endl;
        }
      }
    }
  }

  Assert(!d_errorSet.moreSignals());
  if(result == Result::SAT_UNKNOWN && d_errorSet.errorEmpty()){
    result = Result::SAT;
  }

  d_pivotsInRound.purge();
  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Debug("arith::findModel") << "end findModel() " << instance << " " << result <<  endl;

  return result;
}

//corresponds to Check() in dM06
//template <SimplexDecisionProcedure::PreferenceFunction pf>
bool DualSimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  TimerStat::CodeTimer codeTimer(d_statistics.d_searchTime);

  Debug("arith") << "searchForFeasibleSolution" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0 && !d_errorSet.focusEmpty()){
    if(Debug.isOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }
    Assert(d_conflictVariables.empty());
    ArithVar x_i = d_errorSet.topFocusVariable();

    Debug("arith::update::select") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Debug("arith::update") << "No inconsistent variables" << endl;
      return false; //sat
    }

    --remainingIterations;

    bool useVarOrderPivot = d_pivotsInRound.count(x_i) >=  options::arithPivotThreshold();
    if(!useVarOrderPivot){
      d_pivotsInRound.add(x_i);
    }


    Debug("arith::update")
      << "pivots in rounds: " <<  d_pivotsInRound.count(x_i)
      << " use " << useVarOrderPivot
      << " threshold " << options::arithPivotThreshold()
      << endl;

    LinearEqualityModule::VarPreferenceFunction pf = useVarOrderPivot ?
      &LinearEqualityModule::minVarOrder : &LinearEqualityModule::minBoundAndColLength;

    //DeltaRational beta_i = d_variables.getAssignment(x_i);
    ArithVar x_j = ARITHVAR_SENTINEL;

    int32_t prevErrorSize CVC4_UNUSED = d_errorSet.errorSize();

    if(d_variables.cmpAssignmentLowerBound(x_i) < 0 ){
      x_j = d_linEq.selectSlackUpperBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        Unreachable();
        // ++(d_statistics.d_statUpdateConflicts);
        // reportConflict(x_i);
        // ++(d_statistics.d_simplexConflicts);
        // Node conflict = d_linEq.generateConflictBelowLowerBound(x_i); //unsat
        // d_conflictVariable = x_i;
        // reportConflict(conflict);
        // return true;
      }else{
        const DeltaRational& l_i = d_variables.getLowerBound(x_i);
        d_linEq.pivotAndUpdate(x_i, x_j, l_i);
      }
    }else if(d_variables.cmpAssignmentUpperBound(x_i) > 0){
      x_j = d_linEq.selectSlackLowerBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        Unreachable();
        // ++(d_statistics.d_statUpdateConflicts);
        // reportConflict(x_i);
        // ++(d_statistics.d_simplexConflicts);
        // Node conflict = d_linEq.generateConflictAboveUpperBound(x_i); //unsat
        // d_conflictVariable = x_i;
        // reportConflict(conflict);
        // return true;
      }else{
        const DeltaRational& u_i = d_variables.getUpperBound(x_i);
        d_linEq.pivotAndUpdate(x_i, x_j, u_i);
      }
    }
    Assert(x_j != ARITHVAR_SENTINEL);

    bool conflict = processSignals();
    int32_t currErrorSize CVC4_UNUSED = d_errorSet.errorSize();
    d_pivots++;

    if(Debug.isOn("arith::dual")){
      Debug("arith::dual")
        << "#" << d_pivots
        << " c" << conflict
        << " d" << (prevErrorSize - currErrorSize)
        << " f"  << d_errorSet.inError(x_j)
        << " h" << d_conflictVariables.isMember(x_j)
        << " " << x_i << "->" << x_j
        << endl;
    }

    if(conflict){
      return true;
    }
  }
  Assert(!d_errorSet.focusEmpty() || d_errorSet.errorEmpty());
  Assert(remainingIterations == 0 || d_errorSet.focusEmpty());
  Assert(d_errorSet.noSignals());

  return false;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
