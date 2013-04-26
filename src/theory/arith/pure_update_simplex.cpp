/*********************                                                        */
/*! \file simplex.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/pure_update_simplex.h"
#include "theory/arith/options.h"
#include "theory/arith/constraint.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

PureUpdateSimplexDecisionProcedure::PureUpdateSimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc)
  : SimplexDecisionProcedure(linEq, errors, conflictChannel, tvmalloc)
{ }

Result::Sat PureUpdateSimplexDecisionProcedure::findModel(bool exactResult){
  Assert(d_conflictVariables.empty());

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;

  if(d_errorSet.errorEmpty() && !d_errorSet.moreSignals()){
    Debug("arith::findModel") << "puFindModel("<< instance <<") "
                              << "trivial" << endl;
    return Result::SAT;
  }

  // We need to reduce this because of
  d_errorSet.reduceToSignals();
  d_errorSet.setSelectionRule(VAR_ORDER);

  if(processSignals()){
    d_conflictVariables.purge();

    Debug("arith::findModel") << "puFindModel("<< instance <<") "
                              << "early conflict" << endl;
    return Result::UNSAT;
  }else if(d_errorSet.errorEmpty()){
    Debug("arith::findModel") << "puFindModel("<< instance <<") "
                              << "fixed itself" << endl;
    Assert(!d_errorSet.moreSignals());
    return Result::SAT;
  }

  Debug("arith::findModel") << "puFindModel(" << instance <<") "
                            << "start non-trivial" << endl;

  static const bool verbose = false;
  Result::Sat result = Result::SAT_UNKNOWN;

  if(result == Result::SAT_UNKNOWN){
    if(attemptPureUpdates()){
      result = Result::UNSAT;
    }
    if(result ==  Result::UNSAT){
      ++(d_statistics.d_pureUpdateFoundUnsat);
      if(verbose){ Message() << "pure updates found unsat" << endl; }
    }else if(d_errorSet.errorEmpty()){
      ++(d_statistics.d_pureUpdateFoundSat);
      if(verbose){ Message() << "pure updates found model" << endl; }
    }else{
      ++(d_statistics.d_pureUpdateMissed);
      if(verbose){ Message() << "pure updates missed" << endl; }
    }
  }

  Assert(!d_errorSet.moreSignals());
  if(result == Result::SAT_UNKNOWN && d_errorSet.errorEmpty()){
    result = Result::SAT;
  }

  // ensure that the conflict variable is still in the queue.
  d_conflictVariables.purge();

  Assert(d_focusErrorVar == ARITHVAR_SENTINEL);
  Debug("arith::findModel") << "end findModel() " << instance << " "
                            << result <<  endl;

  return result;
}



PureUpdateSimplexDecisionProcedure::Statistics::Statistics():
  d_pureUpdateFoundUnsat("theory::arith::PureUpdate::FoundUnsat", 0),
  d_pureUpdateFoundSat("theory::arith::PureUpdate::FoundSat", 0),
  d_pureUpdateMissed("theory::arith::PureUpdate::Missed", 0),
  d_pureUpdates("theory::arith::PureUpdate::updates", 0),
  d_pureUpdateDropped("theory::arith::PureUpdate::dropped", 0),
  d_pureUpdateConflicts("theory::arith::PureUpdate::conflicts", 0),
  d_foundConflicts("theory::arith::PureUpdate::foundConflicts", 0),
  d_attemptPureUpdatesTimer("theory::arith::PureUpdate::timer"),
  d_processSignalsTime("theory::arith::PureUpdate::process::timer"),
  d_constructionTimer("theory::arith::PureUpdate::construction::timer")
{
  StatisticsRegistry::registerStat(&d_pureUpdateFoundUnsat);
  StatisticsRegistry::registerStat(&d_pureUpdateFoundSat);
  StatisticsRegistry::registerStat(&d_pureUpdateMissed);
  StatisticsRegistry::registerStat(&d_pureUpdates);
  StatisticsRegistry::registerStat(&d_pureUpdateDropped);
  StatisticsRegistry::registerStat(&d_pureUpdateConflicts);

  StatisticsRegistry::registerStat(&d_foundConflicts);

  StatisticsRegistry::registerStat(&d_attemptPureUpdatesTimer);
  StatisticsRegistry::registerStat(&d_processSignalsTime);
  StatisticsRegistry::registerStat(&d_constructionTimer);
}

PureUpdateSimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_pureUpdateFoundUnsat);
  StatisticsRegistry::unregisterStat(&d_pureUpdateFoundSat);
  StatisticsRegistry::unregisterStat(&d_pureUpdateMissed);
  StatisticsRegistry::unregisterStat(&d_pureUpdates);
  StatisticsRegistry::unregisterStat(&d_pureUpdateDropped);
  StatisticsRegistry::unregisterStat(&d_pureUpdateConflicts);

  StatisticsRegistry::unregisterStat(&d_foundConflicts);

  StatisticsRegistry::unregisterStat(&d_attemptPureUpdatesTimer);
  StatisticsRegistry::unregisterStat(&d_processSignalsTime);
  StatisticsRegistry::unregisterStat(&d_constructionTimer);
}

bool PureUpdateSimplexDecisionProcedure::attemptPureUpdates(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_attemptPureUpdatesTimer);

  Assert(!d_errorSet.focusEmpty());
  Assert(d_errorSet.noSignals());

  d_focusErrorVar = constructInfeasiblityFunction(d_statistics.d_constructionTimer);

  UpdateInfo proposal;
  int boundImprovements = 0;
  int dropped = 0;
  int computations = 0;

  for( Tableau::RowIterator ri = d_tableau.basicRowIterator(d_focusErrorVar); !ri.atEnd(); ++ri){
    const Tableau::Entry& e = *ri;

    ArithVar curr = e.getColVar();
    if(curr == d_focusErrorVar){ continue; }

    int dir = e.getCoefficient().sgn();
    Assert(dir != 0);

    bool worthwhile  = false;

    if( (dir > 0 && d_variables.cmpAssignmentUpperBound(curr) < 0) ||
        (dir < 0 && d_variables.cmpAssignmentLowerBound(curr) > 0) ){

      ++computations;
      proposal = UpdateInfo(curr, dir);
      d_linEq.computeSafeUpdate(proposal, &LinearEqualityModule::noPreference);

      Assert(proposal.errorsChange() <= 0);
      Assert(proposal.focusDirection() >= 0);

      worthwhile = proposal.errorsChange() < 0 ||
        (proposal.focusDirection() > 0 &&
         d_variables.boundCounts(curr).isZero() &&
         !proposal.describesPivot());

      Debug("pu::refined")
        << "pure update proposal "
        << curr << " "
        << worthwhile << " "
        << proposal
        << endl;
    }
    if(worthwhile){
      Debug("pu") << d_variables.getAssignment(d_focusErrorVar) << endl;

      BoundCounts before = d_variables.boundCounts(curr);
      DeltaRational newAssignment =
        d_variables.getAssignment(curr) + proposal.nonbasicDelta();
      d_linEq.updateTracked(curr, newAssignment);
      BoundCounts after = d_variables.boundCounts(curr);

      ++d_statistics.d_pureUpdates;
      ++boundImprovements;
      Debug("pu") << boundImprovements  << ": " << curr
                  << " before: " << before
                  << " after: " << after
                  << e.getCoefficient()
                  << d_variables.getAssignment(d_focusErrorVar) << endl;

      uint32_t prevSize = d_errorSet.errorSize();
      Assert(d_errorSet.moreSignals());
      if(Debug.isOn("pu")){  d_errorSet.debugPrint(Debug("pu")); }
      while(d_errorSet.moreSignals()){
        ArithVar updated = d_errorSet.topSignal();
        bool wasInError = d_errorSet.inError(updated);
        d_errorSet.popSignal();
        if(updated == curr){ continue; }
        Assert(d_tableau.isBasic(updated));
        if(!d_linEq.basicIsTracked(updated)){continue;}


        Assert(d_linEq.basicIsTracked(updated));
        Assert(wasInError || d_variables.assignmentIsConsistent(updated));

        if(!d_variables.assignmentIsConsistent(updated)
           && checkBasicForConflict(updated)){
          Assert(!d_conflictVariables.isMember(updated) );
          Debug("pu")
            << "It worked? "
            << d_statistics.d_pureUpdateConflicts.getData()
            << " " << curr
            << " "  << checkBasicForConflict(updated) << endl;
          reportConflict(updated);
          ++(d_statistics.d_foundConflicts);
          ++(d_statistics.d_pureUpdateConflicts);
        }
      }
      if(d_conflictVariables.empty()){
        if(Debug.isOn("pu")){  d_errorSet.debugPrint(Debug("pu")); }
        uint32_t currSize = d_errorSet.errorSize();
        Assert(currSize <= prevSize);
        if(currSize < prevSize){
          dropped+= prevSize - currSize;
          if(currSize == 0){
            break;
          }
        }
      }else{
        break;
      }
    }
  }

  tearDownInfeasiblityFunction(d_statistics.d_constructionTimer, d_focusErrorVar);
  d_focusErrorVar = ARITHVAR_SENTINEL;

  (d_statistics.d_pureUpdateDropped) += dropped;

  Assert(d_errorSet.noSignals());
  return !d_conflictVariables.empty();
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
