/*********************                                                        */
/*! \file simplex.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "base/output.h"
#include "options/arith_options.h"
#include "theory/arith/constraint.h"
#include "theory/arith/simplex.h"


using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {


SimplexDecisionProcedure::SimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : d_pivots(0)
  , d_conflictVariables()
  , d_linEq(linEq)
  , d_variables(d_linEq.getVariables())
  , d_tableau(d_linEq.getTableau())
  , d_errorSet(errors)
  , d_numVariables(0)
  , d_conflictChannel(conflictChannel)
  , d_conflictBuilder(NULL)
  , d_arithVarMalloc(tvmalloc)
  , d_errorSize(0)
  , d_zero(0)
  , d_posOne(1)
  , d_negOne(-1)
{
  d_heuristicRule = options::arithErrorSelectionRule();
  d_errorSet.setSelectionRule(d_heuristicRule);
  d_conflictBuilder = new FarkasConflictBuilder();
}

SimplexDecisionProcedure::~SimplexDecisionProcedure(){
  delete d_conflictBuilder;
}


bool SimplexDecisionProcedure::standardProcessSignals(TimerStat &timer, IntStat& conflicts) {
  TimerStat::CodeTimer codeTimer(timer);
  Assert( d_conflictVariables.empty() );


  while(d_errorSet.moreSignals()){
    ArithVar curr = d_errorSet.topSignal();
    if(d_tableau.isBasic(curr) && !d_variables.assignmentIsConsistent(curr)){
      Assert(d_linEq.basicIsTracked(curr));

      if(!d_conflictVariables.isMember(curr) && checkBasicForConflict(curr)){

        Debug("recentlyViolated")
          << "It worked? "
          << conflicts.getData()
          << " " << curr
          << " "  << checkBasicForConflict(curr) << endl;
        reportConflict(curr);
        ++conflicts;
      }
    }
    // Pop signal afterwards in case d_linEq.trackVariable(curr);
    // is needed for for the ErrorSet
    d_errorSet.popSignal();
  }
  d_errorSize = d_errorSet.errorSize();

  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
}

/** Reports a conflict to on the output channel. */
void SimplexDecisionProcedure::reportConflict(ArithVar basic){
  Assert(!d_conflictVariables.isMember(basic));
  Assert(checkBasicForConflict(basic));

  ConstraintCP conflicted = generateConflictForBasic(basic);
  Assert(conflicted != NullConstraint);
  d_conflictChannel.raiseConflict(conflicted);

  d_conflictVariables.add(basic);
}

ConstraintCP SimplexDecisionProcedure::generateConflictForBasic(ArithVar basic) const {

  Assert(d_tableau.isBasic(basic));
  Assert(checkBasicForConflict(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    Assert(d_linEq.nonbasicsAtUpperBounds(basic));
    return d_linEq.generateConflictBelowLowerBound(basic, *d_conflictBuilder);
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    Assert(d_linEq.nonbasicsAtLowerBounds(basic));
    return d_linEq.generateConflictAboveUpperBound(basic, *d_conflictBuilder);
  }else{
    Unreachable();
    return NullConstraint;
  }
}
bool SimplexDecisionProcedure::maybeGenerateConflictForBasic(ArithVar basic) const {
  if(checkBasicForConflict(basic)){
    ConstraintCP conflicted = generateConflictForBasic(basic);
    d_conflictChannel.raiseConflict(conflicted);
    return true;
  }else{
    return false;
  }
}

bool SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic) const {
  Assert(d_tableau.isBasic(basic));
  Assert(d_linEq.basicIsTracked(basic));

  if(d_variables.cmpAssignmentLowerBound(basic) < 0){
    if(d_linEq.nonbasicsAtUpperBounds(basic)){
      return true;
    }
  }else if(d_variables.cmpAssignmentUpperBound(basic) > 0){
    if(d_linEq.nonbasicsAtLowerBounds(basic)){
      return true;
    }
  }
  return false;
}

void SimplexDecisionProcedure::tearDownInfeasiblityFunction(TimerStat& timer, ArithVar tmp){
  TimerStat::CodeTimer codeTimer(timer);
  Assert(tmp != ARITHVAR_SENTINEL);
  Assert(d_tableau.isBasic(tmp));

  RowIndex ri = d_tableau.basicToRowIndex(tmp);
  d_linEq.stopTrackingRowIndex(ri);
  d_tableau.removeBasicRow(tmp);
  releaseVariable(tmp);
}

void SimplexDecisionProcedure::shrinkInfeasFunc(TimerStat& timer, ArithVar inf, const ArithVarVec& dropped){
  TimerStat::CodeTimer codeTimer(timer);
  for(ArithVarVec::const_iterator i=dropped.begin(), i_end = dropped.end(); i != i_end; ++i){
    ArithVar back = *i;

    int focusSgn = d_errorSet.focusSgn(back);
    Rational chg(-focusSgn);

    d_linEq.substitutePlusTimesConstant(inf, back, chg);
  }
}

void SimplexDecisionProcedure::adjustInfeasFunc(TimerStat& timer, ArithVar inf, const AVIntPairVec& focusChanges){
  TimerStat::CodeTimer codeTimer(timer);
  for(AVIntPairVec::const_iterator i=focusChanges.begin(), i_end = focusChanges.end(); i != i_end; ++i){
    ArithVar v = (*i).first;
    int focusChange = (*i).second;

    Rational chg(focusChange);
    if(d_tableau.isBasic(v)){
      d_linEq.substitutePlusTimesConstant(inf, v, chg);
    }else{
      d_linEq.directlyAddToCoefficient(inf, v, chg);
    }
  }
}

void SimplexDecisionProcedure::addToInfeasFunc(TimerStat& timer, ArithVar inf, ArithVar e){
  AVIntPairVec justE;
  int sgn  = d_errorSet.getSgn(e);
  justE.push_back(make_pair(e, sgn));
  adjustInfeasFunc(timer, inf, justE);
}

void SimplexDecisionProcedure::removeFromInfeasFunc(TimerStat& timer, ArithVar inf, ArithVar e){
  AVIntPairVec justE;
  int opSgn  = -d_errorSet.getSgn(e);
  justE.push_back(make_pair(e, opSgn));
  adjustInfeasFunc(timer, inf, justE);
}

ArithVar SimplexDecisionProcedure::constructInfeasiblityFunction(TimerStat& timer, const ArithVarVec& set){
  Debug("constructInfeasiblityFunction") << "constructInfeasiblityFunction start" << endl;

  TimerStat::CodeTimer codeTimer(timer);
  Assert(!d_errorSet.focusEmpty());
  Assert(debugIsASet(set));
  
  ArithVar inf = requestVariable();
  Assert(inf != ARITHVAR_SENTINEL);

  std::vector<Rational> coeffs;
  std::vector<ArithVar> variables;

  for(ArithVarVec::const_iterator iter = set.begin(), iend = set.end(); iter != iend; ++iter){
    ArithVar e = *iter;

    Assert(d_tableau.isBasic(e));
    Assert(!d_variables.assignmentIsConsistent(e));

    int sgn = d_errorSet.getSgn(e);
    Assert(sgn == -1 || sgn == 1);
    const Rational& violatedCoeff = sgn < 0 ? d_negOne : d_posOne;
    coeffs.push_back(violatedCoeff);
    variables.push_back(e);

    Debug("constructInfeasiblityFunction") << violatedCoeff << " " << e << endl;

  }
  d_tableau.addRow(inf, coeffs, variables);
  DeltaRational newAssignment = d_linEq.computeRowValue(inf, false);
  d_variables.setAssignment(inf, newAssignment);

  //d_linEq.trackVariable(inf);
  d_linEq.trackRowIndex(d_tableau.basicToRowIndex(inf));

  Debug("constructInfeasiblityFunction") << inf << " " << newAssignment << endl;
  Debug("constructInfeasiblityFunction") << "constructInfeasiblityFunction done" << endl;
  return inf;
}

ArithVar SimplexDecisionProcedure::constructInfeasiblityFunction(TimerStat& timer){
  ArithVarVec inError;
  d_errorSet.pushFocusInto(inError);
  return constructInfeasiblityFunction(timer, inError);
}

ArithVar SimplexDecisionProcedure::constructInfeasiblityFunction(TimerStat& timer, ArithVar e){
  ArithVarVec justE;
  justE.push_back(e);
  return constructInfeasiblityFunction(timer, justE);
}

void SimplexDecisionProcedure::addSgn(sgn_table& sgns, ArithVar col, int sgn, ArithVar basic){
  pair<ArithVar, int> p = make_pair(col, determinizeSgn(sgn));
  sgns[p].push_back(basic);
}

void SimplexDecisionProcedure::addRowSgns(sgn_table& sgns, ArithVar basic, int norm){
  for(Tableau::RowIterator i = d_tableau.basicRowIterator(basic); !i.atEnd(); ++i){
    const Tableau::Entry& entry = *i;
    ArithVar v = entry.getColVar();
    int sgn = (entry.getCoefficient().sgn());
    addSgn(sgns, v, norm * sgn, basic);
  }
}

ArithVar SimplexDecisionProcedure::find_basic_in_sgns(const sgn_table& sgns, ArithVar col, int sgn, const DenseSet& m, bool inside){
  pair<ArithVar, int> p = make_pair(col, determinizeSgn(sgn));
  sgn_table::const_iterator i = sgns.find(p);

  if(i != sgns.end()){
    const ArithVarVec& vec = (*i).second;
    for(ArithVarVec::const_iterator viter = vec.begin(), vend = vec.end(); viter != vend; ++viter){
      ArithVar curr = *viter;
      if(inside == m.isMember(curr)){
        return curr;
      }
    }
  }
  return ARITHVAR_SENTINEL;
}

SimplexDecisionProcedure::sgn_table::const_iterator SimplexDecisionProcedure::find_sgns(const sgn_table& sgns, ArithVar col, int sgn){
  pair<ArithVar, int> p = make_pair(col, determinizeSgn(sgn));
  return sgns.find(p);
}
}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
