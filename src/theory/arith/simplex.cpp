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

using namespace std;

using namespace CVC4;
using namespace CVC4::kind;

using namespace CVC4::theory;
using namespace CVC4::theory::arith;


static const uint32_t NUM_CHECKS = 10;
static const bool CHECK_AFTER_PIVOT = true;
static const uint32_t VARORDER_CHECK_PERIOD = 200;

SimplexDecisionProcedure::SimplexDecisionProcedure(ArithPropManager& propManager,
                                                   ArithPartialModel& pm,
                                                   Tableau& tableau) :
  d_partialModel(pm),
  d_tableau(tableau),
  d_queue(pm, tableau),
  d_propManager(propManager),
  d_numVariables(0),
  d_delayedLemmas(),
  d_pivotsInRound(),
  d_ZERO(0),
  d_DELTA_ZERO(0,0)
{
  switch(Options::ArithPivotRule rule = Options::current()->pivotRule) {
  case Options::MINIMUM:
    d_queue.setPivotRule(ArithPriorityQueue::MINIMUM);
    break;
  case Options::BREAK_TIES:
    d_queue.setPivotRule(ArithPriorityQueue::BREAK_TIES);
    break;
  case Options::MAXIMUM:
    d_queue.setPivotRule(ArithPriorityQueue::MAXIMUM);
    break;
  default:
    Unhandled(rule);
  }
}

SimplexDecisionProcedure::Statistics::Statistics():
  d_statPivots("theory::arith::pivots",0),
  d_statUpdates("theory::arith::updates",0),
  d_statAssertUpperConflicts("theory::arith::AssertUpperConflicts", 0),
  d_statAssertLowerConflicts("theory::arith::AssertLowerConflicts", 0),
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
  d_boundComputationTime("theory::arith::bound::time"),
  d_boundComputations("theory::arith::bound::boundComputations",0),
  d_boundPropagations("theory::arith::bound::boundPropagations",0),
  d_delayedConflicts("theory::arith::delayedConflicts",0),
  d_pivotTime("theory::arith::pivotTime"),
  d_avgNumRowsNotContainingOnUpdate("theory::arith::avgNumRowsNotContainingOnUpdate"),
  d_avgNumRowsNotContainingOnPivot("theory::arith::avgNumRowsNotContainingOnPivot")
{
  StatisticsRegistry::registerStat(&d_statPivots);
  StatisticsRegistry::registerStat(&d_statUpdates);
  StatisticsRegistry::registerStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::registerStat(&d_statAssertLowerConflicts);
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

  StatisticsRegistry::registerStat(&d_boundComputationTime);
  StatisticsRegistry::registerStat(&d_boundComputations);
  StatisticsRegistry::registerStat(&d_boundPropagations);

  StatisticsRegistry::registerStat(&d_delayedConflicts);

  StatisticsRegistry::registerStat(&d_pivotTime);

  StatisticsRegistry::registerStat(&d_avgNumRowsNotContainingOnUpdate);
  StatisticsRegistry::registerStat(&d_avgNumRowsNotContainingOnPivot);
}

SimplexDecisionProcedure::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statPivots);
  StatisticsRegistry::unregisterStat(&d_statUpdates);
  StatisticsRegistry::unregisterStat(&d_statAssertUpperConflicts);
  StatisticsRegistry::unregisterStat(&d_statAssertLowerConflicts);
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

  StatisticsRegistry::unregisterStat(&d_boundComputationTime);
  StatisticsRegistry::unregisterStat(&d_boundComputations);
  StatisticsRegistry::unregisterStat(&d_boundPropagations);

  StatisticsRegistry::unregisterStat(&d_delayedConflicts);
  StatisticsRegistry::unregisterStat(&d_pivotTime);

  StatisticsRegistry::unregisterStat(&d_avgNumRowsNotContainingOnUpdate);
  StatisticsRegistry::unregisterStat(&d_avgNumRowsNotContainingOnPivot);
}

/* procedure AssertLower( x_i >= c_i ) */
Node SimplexDecisionProcedure::AssertLower(ArithVar x_i, const DeltaRational& c_i, TNode original){
  Debug("arith") << "AssertLower(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_partialModel.belowLowerBound(x_i, c_i, true)){
    return Node::null();
  }

  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    //d_out->conflict(conflict);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    ++(d_statistics.d_statAssertLowerConflicts);
    return conflict;
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

  d_updatedBounds.softAdd(x_i);

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) < c_i){
      update(x_i, c_i);
    }
  }else{
    d_queue.enqueueIfInconsistent(x_i);
  }

  if(Debug.isOn("model")) { d_partialModel.printModel(x_i); }

  return Node::null();
}

/* procedure AssertUpper( x_i <= c_i) */
Node SimplexDecisionProcedure::AssertUpper(ArithVar x_i, const DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertUpper(" << x_i << " " << c_i << ")"<< std::endl;

  if(d_partialModel.aboveUpperBound(x_i, c_i, true) ){ // \upperbound(x_i) <= c_i
    return Node::null(); //sat
  }

  if(d_partialModel.belowLowerBound(x_i, c_i, true)){// \lowerbound(x_i) > c_i
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    ++(d_statistics.d_statAssertUpperConflicts);
    return conflict;
  }

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

  d_updatedBounds.softAdd(x_i);

  if(!d_tableau.isBasic(x_i)){
    if(d_partialModel.getAssignment(x_i) > c_i){
      update(x_i, c_i);
    }
  }else{
    d_queue.enqueueIfInconsistent(x_i);
  }

  if(Debug.isOn("model")) { d_partialModel.printModel(x_i); }

  return Node::null();
}


/* procedure AssertLower( x_i == c_i ) */
Node SimplexDecisionProcedure::AssertEquality(ArithVar x_i, const DeltaRational& c_i, TNode original){

  Debug("arith") << "AssertEquality(" << x_i << " " << c_i << ")"<< std::endl;

  // u_i <= c_i <= l_i
  // This can happen if both c_i <= x_i and x_i <= c_i are in the system.
  if(d_partialModel.belowLowerBound(x_i, c_i, false) &&
     d_partialModel.aboveUpperBound(x_i, c_i, false)){
    return Node::null(); //sat
  }

  if(d_partialModel.aboveUpperBound(x_i, c_i, true)){
    Node ubc = d_partialModel.getUpperConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, ubc, original);
    Debug("arith") << "AssertLower conflict " << conflict << endl;
    return conflict;
  }

  if(d_partialModel.belowLowerBound(x_i, c_i, true)){
    Node lbc = d_partialModel.getLowerConstraint(x_i);
    Node conflict =  NodeManager::currentNM()->mkNode(AND, lbc, original);
    Debug("arith") << "AssertUpper conflict " << conflict << endl;
    return conflict;
  }

  d_partialModel.setLowerConstraint(x_i,original);
  d_partialModel.setLowerBound(x_i, c_i);

  d_partialModel.setUpperConstraint(x_i,original);
  d_partialModel.setUpperBound(x_i, c_i);

  d_updatedBounds.softAdd(x_i);

  if(!d_tableau.isBasic(x_i)){
    if(!(d_partialModel.getAssignment(x_i) == c_i)){
      update(x_i, c_i);
    }
  }else{
    d_queue.enqueueIfInconsistent(x_i);
  }
  return Node::null();
}

void SimplexDecisionProcedure::update(ArithVar x_i, const DeltaRational& v){
  Assert(!d_tableau.isBasic(x_i));
  DeltaRational assignment_x_i = d_partialModel.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  //Assert(matchingSets(d_tableau, x_i));
  Tableau::ColIterator basicIter = d_tableau.colIterator(x_i);
  for(; !basicIter.atEnd(); ++basicIter){
    const TableauEntry& entry = *basicIter;
    Assert(entry.getColVar() == x_i);

    ArithVar x_j = entry.getRowVar();
    //ReducedRowVector& row_j = d_tableau.lookup(x_j);

    //const Rational& a_ji = row_j.lookup(x_i);
    const Rational& a_ji = entry.getCoefficient();

    const DeltaRational& assignment = d_partialModel.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    d_partialModel.setAssignment(x_j, nAssignment);

    d_queue.enqueueIfInconsistent(x_j);
  }

  d_partialModel.setAssignment(x_i, v);

  Assert(d_tableau.getNumRows() >= d_tableau.getRowLength(x_i));
  double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowLength(x_i));

  (d_statistics.d_avgNumRowsNotContainingOnUpdate).addEntry(difference);
  if(Debug.isOn("paranoid:check_tableau")){  debugCheckTableau(); }
}


bool SimplexDecisionProcedure::propagateCandidateBound(ArithVar basic, bool upperBound){

  DeltaRational bound = upperBound ?
    computeUpperBound(basic):
    computeLowerBound(basic);

  if((upperBound && d_partialModel.strictlyBelowUpperBound(basic, bound)) ||
     (!upperBound && d_partialModel.strictlyAboveLowerBound(basic, bound))){
    Node bestImplied = upperBound ?
      d_propManager.getBestImpliedUpperBound(basic, bound):
      d_propManager.getBestImpliedLowerBound(basic, bound);

    if(!bestImplied.isNull()){
      bool asserted = d_propManager.isAsserted(bestImplied);
      bool propagated = d_propManager.isPropagated(bestImplied);
      if( !asserted && !propagated){

        NodeBuilder<> nb(kind::AND);
        if(upperBound){
          explainNonbasicsUpperBound(basic, nb);
        }else{
          explainNonbasicsLowerBound(basic, nb);
        }
        Node explanation = nb;
        d_propManager.propagate(bestImplied, explanation, false);
        return true;
      }else{
        Debug("arith::prop") << basic << " " << asserted << " " << propagated << endl;
      }
    }
  }
  return false;
}


bool SimplexDecisionProcedure::hasBounds(ArithVar basic, bool upperBound){
  for(Tableau::RowIterator iter = d_tableau.rowIterator(basic); !iter.atEnd(); ++iter){
    const TableauEntry& entry = *iter;

    ArithVar var = entry.getColVar();
    if(var == basic) continue;
    int sgn = entry.getCoefficient().sgn();
    if(upperBound){
      if( (sgn < 0 && !d_partialModel.hasLowerBound(var)) ||
          (sgn > 0 && !d_partialModel.hasUpperBound(var))){
        return false;
      }
    }else{
      if( (sgn < 0 && !d_partialModel.hasUpperBound(var)) ||
          (sgn > 0 && !d_partialModel.hasLowerBound(var))){
        return false;
      }
    }
  }
  return true;
}
void SimplexDecisionProcedure::propagateCandidate(ArithVar basic){
  bool success = false;
  if(d_partialModel.strictlyAboveLowerBound(basic) && hasLowerBounds(basic)){
    ++d_statistics.d_boundComputations;
    success |= propagateCandidateLowerBound(basic);
  }
  if(d_partialModel.strictlyBelowUpperBound(basic) && hasUpperBounds(basic)){
    ++d_statistics.d_boundComputations;
    success |= propagateCandidateUpperBound(basic);
  }
  if(success){
    ++d_statistics.d_boundPropagations;
  }
}

void SimplexDecisionProcedure::propagateCandidates(){
  TimerStat::CodeTimer codeTimer(d_statistics.d_boundComputationTime);

  Assert(d_candidateBasics.empty());

  if(d_updatedBounds.empty()){ return; }

  PermissiveBackArithVarSet::const_iterator i = d_updatedBounds.begin();
  PermissiveBackArithVarSet::const_iterator end = d_updatedBounds.end();
  for(; i != end; ++i){
    ArithVar var = *i;
    if(d_tableau.isBasic(var) &&
       d_tableau.getRowLength(var) <= Options::current()->arithPropagateMaxLength){
      d_candidateBasics.softAdd(var);
    }else{
      Tableau::ColIterator basicIter = d_tableau.colIterator(var);
      for(; !basicIter.atEnd(); ++basicIter){
        const TableauEntry& entry = *basicIter;
        ArithVar rowVar = entry.getRowVar();
        Assert(entry.getColVar() == var);
        Assert(d_tableau.isBasic(rowVar));
        if(d_tableau.getRowLength(rowVar) <= Options::current()->arithPropagateMaxLength){
          d_candidateBasics.softAdd(rowVar);
        }
      }
    }
  }
  d_updatedBounds.purge();

  while(!d_candidateBasics.empty()){
    ArithVar candidate = d_candidateBasics.pop_back();
    Assert(d_tableau.isBasic(candidate));
    propagateCandidate(candidate); 
  }
}


void SimplexDecisionProcedure::debugPivotSimplex(ArithVar x_i, ArithVar x_j){
  Debug("arith::simplex:row") << "debugRowSimplex("
                              << x_i  << "|->" << x_j
                              << ")" << endl;

  for(Tableau::RowIterator iter = d_tableau.rowIterator(x_i); !iter.atEnd(); ++iter){
    const TableauEntry& entry = *iter;

    ArithVar var = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    DeltaRational beta = d_partialModel.getAssignment(var);
    Debug("arith::simplex:row") << var << beta << coeff;
    if(d_partialModel.hasLowerBound(var)){
      Debug("arith::simplex:row") << "(lb " << d_partialModel.getLowerBound(var) << ")";
    }
    if(d_partialModel.hasUpperBound(var)){
      Debug("arith::simplex:row") << "(up " << d_partialModel.getUpperBound(var) << ")";
    }
    Debug("arith::simplex:row") << endl;
  }
  Debug("arith::simplex:row") << "end row"<< endl;
}

void SimplexDecisionProcedure::pivotAndUpdate(ArithVar x_i, ArithVar x_j, DeltaRational& v){
  Assert(x_i != x_j);

  TimerStat::CodeTimer codeTimer(d_statistics.d_pivotTime);

  if(Debug.isOn("arith::simplex:row")){ debugPivotSimplex(x_i, x_j); }

  const TableauEntry& entry_ij =  d_tableau.findEntry(x_i, x_j);
  Assert(!entry_ij.blank());


  const Rational& a_ij = entry_ij.getCoefficient();


  const DeltaRational& betaX_i = d_partialModel.getAssignment(x_i);

  Rational inv_aij = a_ij.inverse();
  DeltaRational theta = (v - betaX_i)*inv_aij;

  d_partialModel.setAssignment(x_i, v);


  DeltaRational tmp = d_partialModel.getAssignment(x_j) + theta;
  d_partialModel.setAssignment(x_j, tmp);


  //Assert(matchingSets(d_tableau, x_j));
  for(Tableau::ColIterator iter = d_tableau.colIterator(x_j); !iter.atEnd(); ++iter){
    const TableauEntry& entry = *iter;
    Assert(entry.getColVar() == x_j);
    ArithVar x_k = entry.getRowVar();
    if(x_k != x_i ){
      const Rational& a_kj = entry.getCoefficient();
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + (theta * a_kj);
      d_partialModel.setAssignment(x_k, nextAssignment);

      d_queue.enqueueIfInconsistent(x_k);
    }
  }

  // Pivots
  ++(d_statistics.d_statPivots);

  Assert(d_tableau.getNumRows() >= d_tableau.getRowLength(x_j));
  double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowLength(x_j));
  (d_statistics.d_avgNumRowsNotContainingOnPivot).addEntry(difference);
  d_tableau.pivot(x_i, x_j);


  d_queue.enqueueIfInconsistent(x_j);

  if(Debug.isOn("tableau")){
    d_tableau.printTableau();
  }
}

ArithVar SimplexDecisionProcedure::minVarOrder(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y){
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!simp.d_tableau.isBasic(x));
  Assert(!simp.d_tableau.isBasic(y));
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

  for(Tableau::RowIterator iter = d_tableau.rowIterator(x_i); !iter.atEnd();  ++iter){
    const TableauEntry& entry = *iter;
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

Node SimplexDecisionProcedure::findConflictOnTheQueue(SearchPeriod type, bool returnFirst) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_findConflictOnTheQueueTime);

  switch(type){
  case BeforeDiffSearch:     ++(d_statistics.d_attemptBeforeDiffSearch); break;
  case DuringDiffSearch:     ++(d_statistics.d_attemptDuringDiffSearch); break;
  case AfterDiffSearch:      ++(d_statistics.d_attemptAfterDiffSearch); break;
  case DuringVarOrderSearch: ++(d_statistics.d_attemptDuringVarOrderSearch); break;
  case AfterVarOrderSearch:  ++(d_statistics.d_attemptAfterVarOrderSearch); break;
  }

  bool success = false;
  Node firstConflict = Node::null();
  ArithPriorityQueue::const_iterator i = d_queue.begin();
  ArithPriorityQueue::const_iterator end = d_queue.end();
  for(; i != end; ++i){
    ArithVar x_i = *i;

    if(d_tableau.isBasic(x_i)){
      Node possibleConflict = checkBasicForConflict(x_i);
      if(!possibleConflict.isNull()){
        success = true;
        if(returnFirst && firstConflict.isNull()){
          firstConflict = possibleConflict;
        }else{
          delayConflictAsLemma(possibleConflict);
        }
      }
    }
  }
  if(success){
    switch(type){
    case BeforeDiffSearch:     ++(d_statistics.d_successBeforeDiffSearch); break;
    case DuringDiffSearch:     ++(d_statistics.d_successDuringDiffSearch); break;
    case AfterDiffSearch:      ++(d_statistics.d_successAfterDiffSearch); break;
    case DuringVarOrderSearch: ++(d_statistics.d_successDuringVarOrderSearch); break;
    case AfterVarOrderSearch:  ++(d_statistics.d_successAfterVarOrderSearch); break;
    }
  }
  return firstConflict;
}

Node SimplexDecisionProcedure::updateInconsistentVars(){
  if(d_queue.empty()){
    return Node::null();
  }

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;
  Debug("arith::updateInconsistentVars") << "begin updateInconsistentVars() "
                                         << instance << endl;

  d_queue.transitionToDifferenceMode();

  Node possibleConflict = Node::null();
  if(d_queue.size() > 1){
    possibleConflict = findConflictOnTheQueue(BeforeDiffSearch);
  }
  if(possibleConflict.isNull()){
    uint32_t numHueristicPivots = d_numVariables + 1;
    uint32_t pivotsRemaining = numHueristicPivots;
    uint32_t pivotsPerCheck = (numHueristicPivots/NUM_CHECKS) + (NUM_CHECKS-1);
    while(!d_queue.empty() &&
          possibleConflict.isNull() &&
          pivotsRemaining > 0){
      uint32_t pivotsToDo = min(pivotsPerCheck, pivotsRemaining);
      possibleConflict = searchForFeasibleSolution(pivotsToDo);
      pivotsRemaining -= pivotsToDo;
      //Once every CHECK_PERIOD examine the entire queue for conflicts
      if(possibleConflict.isNull()){
        possibleConflict = findConflictOnTheQueue(DuringDiffSearch);
      }else{
        findConflictOnTheQueue(AfterDiffSearch, false);
      }
    }
  }

  if(!d_queue.empty() && possibleConflict.isNull()){
    d_queue.transitionToVariableOrderMode();

    while(!d_queue.empty() && possibleConflict.isNull()){
      possibleConflict = searchForFeasibleSolution(VARORDER_CHECK_PERIOD);

      //Once every CHECK_PERIOD examine the entire queue for conflicts
      if(possibleConflict.isNull()){
        possibleConflict = findConflictOnTheQueue(DuringVarOrderSearch);
      }else{
        findConflictOnTheQueue(AfterVarOrderSearch, false);
      }
    }
  }

  Assert(!possibleConflict.isNull() || d_queue.empty());

  // Curiously the invariant that we always do a full check
  // means that the assignment we can always empty these queues.
  d_queue.clear();
  d_pivotsInRound.purge();

  Assert(!d_queue.inCollectionMode());
  d_queue.transitionToCollectionMode();


  Assert(d_queue.inCollectionMode());

  Debug("arith::updateInconsistentVars") << "end updateInconsistentVars() "
                                         << instance << endl;

  return possibleConflict;
}

Node SimplexDecisionProcedure::checkBasicForConflict(ArithVar basic){

  Assert(d_tableau.isBasic(basic));
  const DeltaRational& beta = d_partialModel.getAssignment(basic);

  if(d_partialModel.belowLowerBound(basic, beta, true)){
    ArithVar x_j = selectSlackUpperBound(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictBelowLowerBound(basic);
    }
  }else if(d_partialModel.aboveUpperBound(basic, beta, true)){
    ArithVar x_j = selectSlackLowerBound(basic);
    if(x_j == ARITHVAR_SENTINEL ){
      return generateConflictAboveUpperBound(basic);
    }
  }
  return Node::null();
}

//corresponds to Check() in dM06
//template <SimplexDecisionProcedure::PreferenceFunction pf>
Node SimplexDecisionProcedure::searchForFeasibleSolution(uint32_t remainingIterations){
  Debug("arith") << "updateInconsistentVars" << endl;
  Assert(remainingIterations > 0);

  while(remainingIterations > 0){
    if(Debug.isOn("paranoid:check_tableau")){ debugCheckTableau(); }

    ArithVar x_i = d_queue.dequeueInconsistentBasicVariable();
    Debug("arith::update::select") << "selectSmallestInconsistentVar()=" << x_i << endl;
    if(x_i == ARITHVAR_SENTINEL){
      Debug("arith_update") << "No inconsistent variables" << endl;
      return Node::null(); //sat
    }

    --remainingIterations;

    bool useVarOrderPivot = d_pivotsInRound.count(x_i) >=  Options::current()->arithPivotThreshold;
    if(!useVarOrderPivot){
      d_pivotsInRound.addMultiset(x_i);
    }


    Debug("playground") << "pivots in rounds: " <<  d_pivotsInRound.count(x_i)
                        << " use " << useVarOrderPivot
                        << " threshold " << Options::current()->arithPivotThreshold
                        << endl;

    PreferenceFunction pf = useVarOrderPivot ? minVarOrder : minBoundAndRowCount;

    DeltaRational beta_i = d_partialModel.getAssignment(x_i);
    ArithVar x_j = ARITHVAR_SENTINEL;

    if(d_partialModel.belowLowerBound(x_i, beta_i, true)){
      x_j = selectSlackUpperBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictBelowLowerBound(x_i); //unsat
      }
      DeltaRational l_i = d_partialModel.getLowerBound(x_i);
      pivotAndUpdate(x_i, x_j, l_i);

    }else if(d_partialModel.aboveUpperBound(x_i, beta_i, true)){
      x_j = selectSlackLowerBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        return generateConflictAboveUpperBound(x_i); //unsat
      }
      DeltaRational u_i = d_partialModel.getUpperBound(x_i);
      pivotAndUpdate(x_i, x_j, u_i);
    }
    Assert(x_j != ARITHVAR_SENTINEL);

    //Check to see if we already have a conflict with x_j to prevent wasteful work
    if(CHECK_AFTER_PIVOT){
      Node possibleConflict = checkBasicForConflict(x_j);
      if(!possibleConflict.isNull()){
        return possibleConflict;
      }
    }
  }
  Assert(remainingIterations == 0);

  return Node::null();
}

template <bool upperBound>
void SimplexDecisionProcedure::explainNonbasics(ArithVar basic, NodeBuilder<>& output){
  Assert(d_tableau.isBasic(basic));

  Debug("arith::explainNonbasics") << "SimplexDecisionProcedure::explainNonbasics("
                                   << basic <<") start" << endl;


  Tableau::RowIterator iter = d_tableau.rowIterator(basic);
  for(; !iter.atEnd(); ++iter){
    const TableauEntry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == basic) continue;

    const Rational& a_ij = entry.getCoefficient();
    Assert(a_ij != d_ZERO);
    TNode bound = TNode::null();

    int sgn = a_ij.sgn();
    Assert(sgn != 0);
    if(upperBound){
      if(sgn < 0){
        bound = d_partialModel.getLowerConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_partialModel.getUpperConstraint(nonbasic);
      }
    }else{
      if(sgn < 0){
        bound =  d_partialModel.getUpperConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound =  d_partialModel.getLowerConstraint(nonbasic);
      }
    }
    Assert(!bound.isNull());
    Debug("arith::explainNonbasics") << "\t" << nonbasic << " " << sgn << " " << bound
                                     << endl;
    output << bound;
  }
  Debug("arith::explainNonbasics") << "SimplexDecisionProcedure::explainNonbasics("
                                   << basic << ") done" << endl;
}


TNode SimplexDecisionProcedure::weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v, const Rational& coeff, bool& anyWeakening, ArithVar basic){

  int sgn = coeff.sgn();
  bool ub = aboveUpper?(sgn < 0) : (sgn > 0);
  TNode exp = ub ?
    d_partialModel.getUpperConstraint(v) :
    d_partialModel.getLowerConstraint(v);
  DeltaRational bound = ub?
    d_partialModel.getUpperBound(v) :
    d_partialModel.getLowerBound(v);

  bool weakened;
  do{
    weakened = false;

    Node weaker = ub?
      d_propManager.strictlyWeakerAssertedUpperBound(v, bound):
      d_propManager.strictlyWeakerAssertedLowerBound(v, bound);

    if(!weaker.isNull()){
      DeltaRational weakerBound = asDeltaRational(weaker);

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
                      << "  " << bound << exp << endl
                      << "  " << weakerBound << weaker << endl;

        if(exp.getKind() == AND){
          Debug("weak") << "VICTORY" << endl;
        }

        Assert(diff > d_DELTA_ZERO);
        exp = weaker;
        bound = weakerBound;
      }
    }
  }while(weakened);

  if(exp.getKind() == AND){
    Debug("weak") << "boo: " << exp << endl;
  }
  return exp;
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
  for(Tableau::RowIterator i = d_tableau.rowIterator(basicVar); !i.atEnd(); ++i){
    const TableauEntry& entry = *i;
    ArithVar v = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    conflict << weakestExplanation(aboveUpper, surplus, v, coeff, anyWeakenings, basicVar);
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

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational SimplexDecisionProcedure::computeRowValue(ArithVar x, bool useSafe){
  Assert(d_tableau.isBasic(x));
  DeltaRational sum(0);

  for(Tableau::RowIterator i = d_tableau.rowIterator(x); !i.atEnd(); ++i){
    const TableauEntry& entry = (*i);
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x) continue;
    const Rational& coeff = entry.getCoefficient();

    const DeltaRational& assignment = d_partialModel.getAssignment(nonbasic, useSafe);
    sum = sum + (assignment * coeff);
  }
  return sum;
}

DeltaRational SimplexDecisionProcedure::computeBound(ArithVar basic, bool upperBound){
  DeltaRational sum(0,0);
  for(Tableau::RowIterator i = d_tableau.rowIterator(basic); !i.atEnd(); ++i){
    const TableauEntry& entry = (*i);
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == basic) continue;
    const Rational& coeff =  entry.getCoefficient();
    int sgn = coeff.sgn();
    bool ub = upperBound ? (sgn > 0) : (sgn < 0);

    const DeltaRational& bound = ub ?
      d_partialModel.getUpperBound(nonbasic):
      d_partialModel.getLowerBound(nonbasic);

    DeltaRational diff = bound * coeff;
    sum = sum + diff;
  }
  return sum;
}

/**
 * This check is quite expensive.
 * It should be wrapped in a Debug.isOn() guard.
 *   if(Debug.isOn("paranoid:check_tableau")){
 *      checkTableau();
 *   }
 */
void SimplexDecisionProcedure::debugCheckTableau(){
  ArithVarSet::const_iterator basicIter = d_tableau.beginBasic();
  ArithVarSet::const_iterator endIter = d_tableau.endBasic();
  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    Tableau::RowIterator nonbasicIter = d_tableau.rowIterator(basic);
    for(; !nonbasicIter.atEnd(); ++nonbasicIter){
      const TableauEntry& entry = *nonbasicIter;
      ArithVar nonbasic = entry.getColVar();
      if(basic == nonbasic) continue;

      const Rational& coeff = entry.getCoefficient();
      DeltaRational beta = d_partialModel.getAssignment(nonbasic);
      Debug("paranoid:check_tableau") << nonbasic << beta << coeff<<endl;
      sum = sum + (beta*coeff);
    }
    DeltaRational shouldBe = d_partialModel.getAssignment(basic);
    Debug("paranoid:check_tableau") << "ending row" << sum
                                    << "," << shouldBe << endl;

    Assert(sum == shouldBe);
  }
}

