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
 * DPLL(T) decision procedure.
 */
#include "theory/arith/linear/dual_simplex.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "smt/env.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/error_set.h"
#include "theory/arith/linear/linear_equality.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

DualSimplexDecisionProcedure::DualSimplexDecisionProcedure(
    Env& env,
    LinearEqualityModule& linEq,
    ErrorSet& errors,
    RaiseConflict conflictChannel,
    TempVarMalloc tvmalloc)
    : SimplexDecisionProcedure(env, linEq, errors, conflictChannel, tvmalloc),
      d_pivotsInRound(),
      d_statistics(statisticsRegistry(), d_pivots)
{ }

DualSimplexDecisionProcedure::Statistics::Statistics(StatisticsRegistry& sr,
                                                     uint32_t& pivots)
    : d_statUpdateConflicts(
        sr.registerInt("theory::arith::dual::UpdateConflicts")),
      d_processSignalsTime(
          sr.registerTimer("theory::arith::dual::findConflictOnTheQueueTime")),
      d_simplexConflicts(
          sr.registerInt("theory::arith::dual::simplexConflicts")),
      d_recentViolationCatches(
          sr.registerInt("theory::arith::dual::recentViolationCatches")),
      d_searchTime(sr.registerTimer("theory::arith::dual::searchTime")),
      d_finalCheckPivotCounter(sr.registerReference<uint32_t>(
          "theory::arith::dual::lastPivots", pivots))
{
}

Result::Status DualSimplexDecisionProcedure::dualFindModel(bool exactResult)
{
  Assert(d_conflictVariables.empty());

  d_pivots = 0;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Trace("arith::findModel") << "dualFindModel() trivial" << endl;
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);

  if(processSignals()){
    d_conflictVariables.purge();

    Trace("arith::findModel") << "dualFindModel() early conflict" << endl;
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Trace("arith::findModel") << "dualFindModel() fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    return Result::SAT;
  }

  Trace("arith::findModel") << "dualFindModel() start non-trivial" << endl;

  Result::Status result = Result::UNKNOWN;

  exactResult |= d_varOrderPivotLimit < 0;

  uint32_t checkPeriod = options().arith.arithSimplexCheckPeriod;
  if (result == Result::UNKNOWN)
  {
    uint32_t numDifferencePivots = options().arith.arithHeuristicPivots < 0
                                       ? d_numVariables + 1
                                       : options().arith.arithHeuristicPivots;
    // The signed to unsigned conversion is safe.
    if(numDifferencePivots > 0){

      d_errorSet.setSelectionRule(d_heuristicRule);
      if(searchForFeasibleSolution(numDifferencePivots)){
        result = Result::UNSAT;
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
    }
    else if (d_varOrderPivotLimit > 0)
    {
      d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);
      if (searchForFeasibleSolution(d_varOrderPivotLimit))
      {
        result = Result::UNSAT;
      }
    }
  }

  Assert(!d_errorSet.moreSignals());
  if (result == Result::UNKNOWN && d_errorSet.errorEmpty())
  {
    result = Result::SAT;
  }

  d_pivotsInRound.purge();
  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Trace("arith::findModel") << "end findModel() " << result << endl;

  return result;
}

//corresponds to Check() in dM06
//template <SimplexDecisionProcedure::PreferenceFunction pf>
bool DualSimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  TimerStat::CodeTimer codeTimer(d_statistics.d_searchTime);

  Trace("arith") << "searchForFeasibleSolution" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0 && !d_errorSet.focusEmpty()){
    if(TraceIsOn("paranoid:check_tableau")){ d_linEq.debugCheckTableau(); }
    Assert(d_conflictVariables.empty());
    ArithVar x_i = d_errorSet.topFocusVariable();

    Trace("arith::update::select") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Trace("arith::update") << "No inconsistent variables" << endl;
      return false; //sat
    }

    --remainingIterations;

    bool useVarOrderPivot =
        d_pivotsInRound.count(x_i) >= options().arith.arithPivotThreshold;
    if(!useVarOrderPivot){
      d_pivotsInRound.add(x_i);
    }

    Trace("arith::update") << "pivots in rounds: " << d_pivotsInRound.count(x_i)
                           << " use " << useVarOrderPivot << " threshold "
                           << options().arith.arithPivotThreshold << std::endl;

    LinearEqualityModule::VarPreferenceFunction pf = useVarOrderPivot ?
      &LinearEqualityModule::minVarOrder : &LinearEqualityModule::minBoundAndColLength;

    //DeltaRational beta_i = d_variables.getAssignment(x_i);
    ArithVar x_j = ARITHVAR_SENTINEL;

    int32_t prevErrorSize CVC5_UNUSED = d_errorSet.errorSize();

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
    int32_t currErrorSize CVC5_UNUSED = d_errorSet.errorSize();
    d_pivots++;

    if(TraceIsOn("arith::dual")){
      Trace("arith::dual")
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

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
