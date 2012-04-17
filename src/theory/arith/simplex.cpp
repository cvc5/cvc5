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

SimplexDecisionProcedure::SimplexDecisionProcedure(LinearEqualityModule& linEq, NodeCallBack& conflictChannel) :
  d_linEq(linEq),
  d_partialModel(d_linEq.getPartialModel()),
  d_tableau(d_linEq.getTableau()),
  d_queue(d_partialModel, d_tableau),
  d_numVariables(0),
  d_conflictChannel(conflictChannel),
  d_pivotsInRound(),
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
  d_simplexConflicts("theory::arith::simplexConflicts",0)
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

bool SimplexDecisionProcedure::findConflictOnTheQueue(SearchPeriod type) {
  TimerStat::CodeTimer codeTimer(d_statistics.d_findConflictOnTheQueueTime);

  switch(type){
  case BeforeDiffSearch:     ++(d_statistics.d_attemptBeforeDiffSearch); break;
  case DuringDiffSearch:     ++(d_statistics.d_attemptDuringDiffSearch); break;
  case AfterDiffSearch:      ++(d_statistics.d_attemptAfterDiffSearch); break;
  case DuringVarOrderSearch: ++(d_statistics.d_attemptDuringVarOrderSearch); break;
  case AfterVarOrderSearch:  ++(d_statistics.d_attemptAfterVarOrderSearch); break;
  }

  bool success = false;
  ArithPriorityQueue::const_iterator i = d_queue.begin();
  ArithPriorityQueue::const_iterator end = d_queue.end();
  for(; i != end; ++i){
    ArithVar x_i = *i;

    if(d_tableau.isBasic(x_i)){
      Node possibleConflict = checkBasicForConflict(x_i);
      if(!possibleConflict.isNull()){
        success = true;
        reportConflict(possibleConflict);
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
  return success;
}

bool SimplexDecisionProcedure::findModel(){
  if(d_queue.empty()){
    return false;
  }
  bool foundConflict = false;

  static CVC4_THREADLOCAL(unsigned int) instance = 0;
  instance = instance + 1;
  Debug("arith::findModel") << "begin findModel()" << instance << endl;

  d_queue.transitionToDifferenceMode();

  if(d_queue.size() > 1){
    foundConflict = findConflictOnTheQueue(BeforeDiffSearch);
  }
  if(!foundConflict){
    uint32_t numHeuristicPivots = d_numVariables + 1;
    uint32_t pivotsRemaining = numHeuristicPivots;
    uint32_t pivotsPerCheck = (numHeuristicPivots/NUM_CHECKS) + (NUM_CHECKS-1);
    while(!d_queue.empty() &&
          !foundConflict &&
          pivotsRemaining > 0){
      uint32_t pivotsToDo = min(pivotsPerCheck, pivotsRemaining);
      foundConflict = searchForFeasibleSolution(pivotsToDo);
      pivotsRemaining -= pivotsToDo;
      //Once every CHECK_PERIOD examine the entire queue for conflicts
      if(!foundConflict){
        foundConflict = findConflictOnTheQueue(DuringDiffSearch);
      }else{
        findConflictOnTheQueue(AfterDiffSearch);
      }
    }
  }

  if(!d_queue.empty() && !foundConflict){
    d_queue.transitionToVariableOrderMode();

    while(!d_queue.empty() && !foundConflict){
      foundConflict = searchForFeasibleSolution(VARORDER_CHECK_PERIOD);

      //Once every CHECK_PERIOD examine the entire queue for conflicts
      if(!foundConflict){
        foundConflict = findConflictOnTheQueue(DuringVarOrderSearch);
      } else{
        findConflictOnTheQueue(AfterVarOrderSearch);
      }
    }
  }

  Assert(foundConflict || d_queue.empty());

  // Curiously the invariant that we always do a full check
  // means that the assignment we can always empty these queues.
  d_queue.clear();
  d_pivotsInRound.purge();

  Assert(!d_queue.inCollectionMode());
  d_queue.transitionToCollectionMode();


  Assert(d_queue.inCollectionMode());

  Debug("arith::findModel") << "end findModel() " << instance << endl;

  return foundConflict;
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

    if(d_partialModel.strictlyLessThanLowerBound(x_i, beta_i)){
      x_j = selectSlackUpperBound(x_i, pf);
      if(x_j == ARITHVAR_SENTINEL ){
        ++(d_statistics.d_statUpdateConflicts);
        Node conflict = generateConflictBelowLowerBound(x_i); //unsat
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
  for(Tableau::RowIterator i = d_tableau.rowIterator(basicVar); !i.atEnd(); ++i){
    const TableauEntry& entry = *i;
    ArithVar v = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    bool weakening = false;
    Constraint c = weakestExplanation(aboveUpper, surplus, v, coeff, weakening, basicVar);
    Debug("weak") << "weak : " << weakening << " " << c->assertedToTheTheory()
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

