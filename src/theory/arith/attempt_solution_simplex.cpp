/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */
#include "theory/arith/attempt_solution_simplex.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/constraint.h"
#include "theory/arith/error_set.h"
#include "theory/arith/linear_equality.h"
#include "theory/arith/tableau.h"

using namespace std;

namespace cvc5 {
namespace theory {
namespace arith {

AttemptSolutionSDP::AttemptSolutionSDP(Env& env,
                                       LinearEqualityModule& linEq,
                                       ErrorSet& errors,
                                       RaiseConflict conflictChannel,
                                       TempVarMalloc tvmalloc)
    : SimplexDecisionProcedure(env, linEq, errors, conflictChannel, tvmalloc),
      d_statistics()
{ }

AttemptSolutionSDP::Statistics::Statistics()
    : d_searchTime(smtStatisticsRegistry().registerTimer(
        "theory::arith::attempt::searchTime")),
      d_queueTime(smtStatisticsRegistry().registerTimer(
          "theory::arith::attempt::queueTime")),
      d_conflicts(smtStatisticsRegistry().registerInt(
          "theory::arith::attempt::conflicts"))
{
}

bool AttemptSolutionSDP::matchesNewValue(const DenseMap<DeltaRational>& nv, ArithVar v) const{
  return nv[v] == d_variables.getAssignment(v);
}

Result::Sat AttemptSolutionSDP::attempt(const ApproximateSimplex::Solution& sol){
  const DenseSet& newBasis = sol.newBasis;
  const DenseMap<DeltaRational>& newValues = sol.newValues;

  DenseSet needsToBeAdded;
  for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(!d_tableau.isBasic(b)){
      needsToBeAdded.add(b);
    }
  }
  DenseMap<DeltaRational>::const_iterator nvi = newValues.begin(), nvi_end = newValues.end();
  for(; nvi != nvi_end; ++nvi){
    ArithVar currentlyNb = *nvi;
    if(!d_tableau.isBasic(currentlyNb)){
      if(!matchesNewValue(newValues, currentlyNb)){
        const DeltaRational& newValue = newValues[currentlyNb];
        Trace("arith::updateMany")
          << "updateMany:" << currentlyNb << " "
          << d_variables.getAssignment(currentlyNb) << " to "<< newValue << endl;
        d_linEq.update(currentlyNb, newValue);
        Assert(d_variables.assignmentIsConsistent(currentlyNb));
      }
    }
  }
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(options::ErrorSelectionRule::VAR_ORDER);

  if(processSignals()){
    Debug("arith::findModel") << "attemptSolution() early conflict" << endl;
    d_conflictVariables.purge();
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Debug("arith::findModel") << "attemptSolution() fixed itself" << endl;
    return Result::SAT;
  }

  while(!needsToBeAdded.empty() && !d_errorSet.errorEmpty()){
    ArithVar toRemove = ARITHVAR_SENTINEL;
    ArithVar toAdd = ARITHVAR_SENTINEL;
    DenseSet::const_iterator i = needsToBeAdded.begin(), i_end = needsToBeAdded.end();
    for(; toAdd == ARITHVAR_SENTINEL && i != i_end; ++i){
      ArithVar v = *i;

      Tableau::ColIterator colIter = d_tableau.colIterator(v);
      for(; !colIter.atEnd(); ++colIter){
        const Tableau::Entry& entry = *colIter;
        Assert(entry.getColVar() == v);
        ArithVar b = d_tableau.rowIndexToBasic(entry.getRowIndex());
        if(!newBasis.isMember(b)){
          toAdd = v;

          bool favorBOverToRemove =
            (toRemove == ARITHVAR_SENTINEL) ||
            (matchesNewValue(newValues, toRemove) && !matchesNewValue(newValues, b)) ||
            (d_tableau.basicRowLength(toRemove) > d_tableau.basicRowLength(b));

          if(favorBOverToRemove){
            toRemove = b;
          }
        }
      }
    }
    Assert(toRemove != ARITHVAR_SENTINEL);
    Assert(toAdd != ARITHVAR_SENTINEL);

    Trace("arith::forceNewBasis") << toRemove << " " << toAdd << endl;

    d_linEq.pivotAndUpdate(toRemove, toAdd, newValues[toRemove]);

    Trace("arith::forceNewBasis") << needsToBeAdded.size() << "to go" << endl;
    needsToBeAdded.remove(toAdd);

    bool conflict = processSignals();
    if(conflict){
      d_errorSet.reduceToSignals();
      d_conflictVariables.purge();

      return Result::UNSAT;
    }
  }
  Assert(d_conflictVariables.empty());

  if(d_errorSet.errorEmpty()){
    return Result::SAT;
  }else{
    d_errorSet.reduceToSignals();
    return Result::SAT_UNKNOWN;
  }
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
