/*********************                                                        */
/*! \file linear_equality.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This implements the LinearEqualityModule.
 **
 ** This implements the LinearEqualityModule.
 **/


#include "theory/arith/linear_equality.h"
#include "theory/arith/constraint.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

/* Explicitly instatiate these functions. */
template void LinearEqualityModule::propagateNonbasics<true>(ArithVar basic, Constraint c);
template void LinearEqualityModule::propagateNonbasics<false>(ArithVar basic, Constraint c);

template ArithVar LinearEqualityModule::selectSlack<true>(ArithVar x_i, VarPreferenceFunction pf) const;
template ArithVar LinearEqualityModule::selectSlack<false>(ArithVar x_i, VarPreferenceFunction pf) const;

// template bool LinearEqualityModule::preferNonDegenerate<true>(const UpdateInfo& a, const UpdateInfo& b) const;
// template bool LinearEqualityModule::preferNonDegenerate<false>(const UpdateInfo& a, const UpdateInfo& b) const;

// template bool LinearEqualityModule::preferErrorsFixed<true>(const UpdateInfo& a, const UpdateInfo& b) const;
// template bool LinearEqualityModule::preferErrorsFixed<false>(const UpdateInfo& a, const UpdateInfo& b) const;

template bool LinearEqualityModule::preferWitness<true>(const UpdateInfo& a, const UpdateInfo& b) const;
template bool LinearEqualityModule::preferWitness<false>(const UpdateInfo& a, const UpdateInfo& b) const;


void Border::output(std::ostream& out) const{
  out << "{Border"
      << ", " << d_bound->getVariable()
      << ", " << d_bound->getValue()
      << ", " << d_diff
      << ", " << d_areFixing
      << ", " << d_upperbound;
  if(ownBorder()){
    out << ", ownBorder";
  }else{
    out << ", " << d_entry->getCoefficient();
  }
  out << ", " << d_bound
      << "}";
}

LinearEqualityModule::LinearEqualityModule(ArithVariables& vars, Tableau& t, BoundCountingVector& boundTracking, BasicVarModelUpdateCallBack f):
  d_variables(vars),
  d_tableau(t),
  d_basicVariableUpdates(f),
  d_increasing(1),
  d_decreasing(-1),
  d_relevantErrorBuffer(),
  d_boundTracking(boundTracking),
  d_areTracking(false),
  d_trackCallback(this)
{}

LinearEqualityModule::Statistics::Statistics():
  d_statPivots("theory::arith::pivots",0),
  d_statUpdates("theory::arith::updates",0),
  d_pivotTime("theory::arith::pivotTime"),
  d_adjTime("theory::arith::adjTime"),
  d_weakeningAttempts("theory::arith::weakening::attempts",0),
  d_weakeningSuccesses("theory::arith::weakening::success",0),
  d_weakenings("theory::arith::weakening::total",0),
  d_weakenTime("theory::arith::weakening::time")
{
  StatisticsRegistry::registerStat(&d_statPivots);
  StatisticsRegistry::registerStat(&d_statUpdates);

  StatisticsRegistry::registerStat(&d_pivotTime);
  StatisticsRegistry::registerStat(&d_adjTime);

  StatisticsRegistry::registerStat(&d_weakeningAttempts);
  StatisticsRegistry::registerStat(&d_weakeningSuccesses);
  StatisticsRegistry::registerStat(&d_weakenings);
  StatisticsRegistry::registerStat(&d_weakenTime);
}

LinearEqualityModule::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statPivots);
  StatisticsRegistry::unregisterStat(&d_statUpdates);
  StatisticsRegistry::unregisterStat(&d_pivotTime);
  StatisticsRegistry::unregisterStat(&d_adjTime);


  StatisticsRegistry::unregisterStat(&d_weakeningAttempts);
  StatisticsRegistry::unregisterStat(&d_weakeningSuccesses);
  StatisticsRegistry::unregisterStat(&d_weakenings);
  StatisticsRegistry::unregisterStat(&d_weakenTime);
}
void LinearEqualityModule::includeBoundCountChange(ArithVar nb, BoundCounts prev){
  if(d_tableau.isBasic(nb)){
    return;
  }
  Assert(!d_tableau.isBasic(nb));
  Assert(!d_areTracking);

  BoundCounts curr = d_variables.boundCounts(nb);

  Assert(prev != curr);
  Tableau::ColIterator basicIter = d_tableau.colIterator(nb);
  for(; !basicIter.atEnd(); ++basicIter){
    const Tableau::Entry& entry = *basicIter;
    Assert(entry.getColVar() == nb);
    int a_ijSgn = entry.getCoefficient().sgn();

    ArithVar basic = d_tableau.rowIndexToBasic(entry.getRowIndex());

    BoundCounts& counts = d_boundTracking.get(basic);
    Debug("includeBoundCountChange") << basic << " " << counts << " to " ;
    counts -= prev.multiplyBySgn(a_ijSgn);
    counts += curr.multiplyBySgn(a_ijSgn);
    Debug("includeBoundCountChange") << counts << " " << a_ijSgn << std::endl;
  }
  d_boundTracking.set(nb, curr);
}

void LinearEqualityModule::updateMany(const DenseMap<DeltaRational>& many){
  for(DenseMap<DeltaRational>::const_iterator i = many.begin(), i_end = many.end(); i != i_end; ++i){
    ArithVar nb = *i;
    Assert(!d_tableau.isBasic(nb));
    const DeltaRational& newValue = many[nb];
    if(newValue != d_variables.getAssignment(nb)){
      Trace("arith::updateMany")
        << "updateMany:" << nb << " "
        << d_variables.getAssignment(nb) << " to "<< newValue << endl;
      update(nb, newValue);
    }
  }
}


void LinearEqualityModule::forceNewBasis(const DenseSet& newBasis){
  DenseSet needsToBeAdded;
  for(DenseSet::const_iterator i = newBasis.begin(), i_end = newBasis.end(); i != i_end; ++i){
    ArithVar b = *i;
    if(!d_tableau.isBasic(b)){
      needsToBeAdded.add(b);
    }
  }

  while(!needsToBeAdded.empty()){
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
          if(toRemove == ARITHVAR_SENTINEL ||
             d_tableau.basicRowLength(toRemove) > d_tableau.basicRowLength(b)){
            toRemove = b;
          }
        }
      }
    }
    Assert(toRemove != ARITHVAR_SENTINEL);
    Assert(toAdd != ARITHVAR_SENTINEL);

    Trace("arith::forceNewBasis") << toRemove << " " << toAdd << endl;
    d_tableau.pivot(toRemove, toAdd, d_trackCallback);
    d_basicVariableUpdates(toAdd);

    Trace("arith::forceNewBasis") << needsToBeAdded.size() << "to go" << endl;
    needsToBeAdded.remove(toAdd);
  }
}

void LinearEqualityModule::updateUntracked(ArithVar x_i, const DeltaRational& v){
  Assert(!d_tableau.isBasic(x_i));
  Assert(!d_areTracking);
  const DeltaRational& assignment_x_i = d_variables.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);


  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  Tableau::ColIterator colIter = d_tableau.colIterator(x_i);
  for(; !colIter.atEnd(); ++colIter){
    const Tableau::Entry& entry = *colIter;
    Assert(entry.getColVar() == x_i);

    ArithVar x_j = d_tableau.rowIndexToBasic(entry.getRowIndex());
    const Rational& a_ji = entry.getCoefficient();

    const DeltaRational& assignment = d_variables.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    d_variables.setAssignment(x_j, nAssignment);

    d_basicVariableUpdates(x_j);
  }

  d_variables.setAssignment(x_i, v);

  if(Debug.isOn("paranoid:check_tableau")){  debugCheckTableau(); }
}

void LinearEqualityModule::updateTracked(ArithVar x_i, const DeltaRational& v){
  TimerStat::CodeTimer codeTimer(d_statistics.d_adjTime);

  Assert(!d_tableau.isBasic(x_i));
  Assert(d_areTracking);

  ++(d_statistics.d_statUpdates);

  DeltaRational diff =  v - d_variables.getAssignment(x_i);
  Debug("arith") <<"update " << x_i << ": "
                 << d_variables.getAssignment(x_i) << "|-> " << v << endl;


  BoundCounts before = d_variables.boundCounts(x_i);
  d_variables.setAssignment(x_i, v);
  BoundCounts after = d_variables.boundCounts(x_i);

  bool anyChange = before != after;

  Tableau::ColIterator colIter = d_tableau.colIterator(x_i);
  for(; !colIter.atEnd(); ++colIter){
    const Tableau::Entry& entry = *colIter;
    Assert(entry.getColVar() == x_i);

    ArithVar x_j = d_tableau.rowIndexToBasic(entry.getRowIndex());
    const Rational& a_ji = entry.getCoefficient();

    const DeltaRational& assignment = d_variables.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    Debug("update") << x_j << " " << a_ji << assignment << " -> " << nAssignment << endl;
    d_variables.setAssignment(x_j, nAssignment);

    if(anyChange && basicIsTracked(x_j)){
      BoundCounts& next_bc_k = d_boundTracking.get(x_j);
      next_bc_k.addInChange(a_ji.sgn(), before, after);
    }

    d_basicVariableUpdates(x_j);
  }

  if(Debug.isOn("paranoid:check_tableau")){  debugCheckTableau(); }
}

void LinearEqualityModule::pivotAndUpdate(ArithVar x_i, ArithVar x_j, const DeltaRational& x_i_value){
  Assert(x_i != x_j);

  TimerStat::CodeTimer codeTimer(d_statistics.d_pivotTime);

  static int instance = 0;

  if(Debug.isOn("arith::tracking::pre")){
    ++instance;
    Debug("arith::tracking")  << "pre update #" << instance << endl;
    debugCheckTracking();
  }

  if(Debug.isOn("arith::simplex:row")){ debugPivot(x_i, x_j); }

  RowIndex ridx = d_tableau.basicToRowIndex(x_i);
  const Tableau::Entry& entry_ij =  d_tableau.findEntry(ridx, x_j);
  Assert(!entry_ij.blank());

  const Rational& a_ij = entry_ij.getCoefficient();
  const DeltaRational& betaX_i = d_variables.getAssignment(x_i);
  DeltaRational theta = (x_i_value - betaX_i)/a_ij;
  DeltaRational x_j_value = d_variables.getAssignment(x_j) + theta;

  updateTracked(x_j, x_j_value);

  if(Debug.isOn("arith::tracking::mid")){
    Debug("arith::tracking")  << "postupdate prepivot #" << instance << endl;
    debugCheckTracking();
  }

  // Pivots
  ++(d_statistics.d_statPivots);

  d_tableau.pivot(x_i, x_j, d_trackCallback);

  if(Debug.isOn("arith::tracking::post")){
    Debug("arith::tracking")  << "postpivot #" << instance << endl;
    debugCheckTracking();
  }

  d_basicVariableUpdates(x_j);

  if(Debug.isOn("matrix")){
    d_tableau.printMatrix();
  }
}

uint32_t LinearEqualityModule::updateProduct(const UpdateInfo& inf) const {
  uint32_t colLen = d_tableau.getColLength(inf.nonbasic());
  if(inf.describesPivot()){
    Assert(inf.leaving() != inf.nonbasic());
    return colLen + d_tableau.basicRowLength(inf.leaving());
  }else{
    return colLen;
  }
}

void LinearEqualityModule::debugCheckTracking(){
  Tableau::BasicIterator basicIter = d_tableau.beginBasic(),
    endIter = d_tableau.endBasic();
  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    Debug("arith::tracking") << "arith::tracking row basic: " << basic << endl;

    for(Tableau::RowIterator iter = d_tableau.basicRowIterator(basic); !iter.atEnd() && Debug.isOn("arith::tracking"); ++iter){
      const Tableau::Entry& entry = *iter;

      ArithVar var = entry.getColVar();
      const Rational& coeff = entry.getCoefficient();
      DeltaRational beta = d_variables.getAssignment(var);
      Debug("arith::tracking") << var << " " << d_variables.boundCounts(var)
                               << " " << beta << coeff;
      if(d_variables.hasLowerBound(var)){
        Debug("arith::tracking") << "(lb " << d_variables.getLowerBound(var) << ")";
      }
      if(d_variables.hasUpperBound(var)){
        Debug("arith::tracking") << "(up " << d_variables.getUpperBound(var) << ")";
      }
      Debug("arith::tracking") << endl;
    }
    Debug("arith::tracking") << "end row"<< endl;

    if(basicIsTracked(basic)){
      BoundCounts computed = computeBoundCounts(basic);
      Debug("arith::tracking")
        << "computed " << computed
        << " tracking " << d_boundTracking[basic] << endl;
      Assert(computed == d_boundTracking[basic]);

    }
  }
}

void LinearEqualityModule::debugPivot(ArithVar x_i, ArithVar x_j){
  Debug("arith::pivot") << "debugPivot("<< x_i  <<"|->"<< x_j << ")" << endl;

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;

    ArithVar var = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    DeltaRational beta = d_variables.getAssignment(var);
    Debug("arith::pivot") << var << beta << coeff;
    if(d_variables.hasLowerBound(var)){
      Debug("arith::pivot") << "(lb " << d_variables.getLowerBound(var) << ")";
    }
    if(d_variables.hasUpperBound(var)){
      Debug("arith::pivot") << "(up " << d_variables.getUpperBound(var) << ")";
    }
    Debug("arith::pivot") << endl;
  }
  Debug("arith::pivot") << "end row"<< endl;
}

/**
 * This check is quite expensive.
 * It should be wrapped in a Debug.isOn() guard.
 *   if(Debug.isOn("paranoid:check_tableau")){
 *      checkTableau();
 *   }
 */
void LinearEqualityModule::debugCheckTableau(){
  Tableau::BasicIterator basicIter = d_tableau.beginBasic(),
    endIter = d_tableau.endBasic();
  for(; basicIter != endIter; ++basicIter){
    ArithVar basic = *basicIter;
    DeltaRational sum;
    Debug("paranoid:check_tableau") << "starting row" << basic << endl;
    Tableau::RowIterator nonbasicIter = d_tableau.basicRowIterator(basic);
    for(; !nonbasicIter.atEnd(); ++nonbasicIter){
      const Tableau::Entry& entry = *nonbasicIter;
      ArithVar nonbasic = entry.getColVar();
      if(basic == nonbasic) continue;

      const Rational& coeff = entry.getCoefficient();
      DeltaRational beta = d_variables.getAssignment(nonbasic);
      Debug("paranoid:check_tableau") << nonbasic << beta << coeff<<endl;
      sum = sum + (beta*coeff);
    }
    DeltaRational shouldBe = d_variables.getAssignment(basic);
    Debug("paranoid:check_tableau") << "ending row" << sum
                                    << "," << shouldBe << endl;

    Assert(sum == shouldBe);
  }
}
bool LinearEqualityModule::debugEntireLinEqIsConsistent(const string& s){
  bool result = true;
  for(ArithVar var = 0, end = d_tableau.getNumColumns(); var != end; ++var){
    //  for(VarIter i = d_variables.begin(), end = d_variables.end(); i != end; ++i){
    //ArithVar var = d_arithvarNodeMap.asArithVar(*i);
    if(!d_variables.assignmentIsConsistent(var)){
      d_variables.printModel(var);
      Warning() << s << ":" << "Assignment is not consistent for " << var ;
      if(d_tableau.isBasic(var)){
        Warning() << " (basic)";
      }
      Warning() << endl;
      result = false;
    }
  }
  return result;
}

DeltaRational LinearEqualityModule::computeBound(ArithVar basic, bool upperBound){
  DeltaRational sum(0,0);
  for(Tableau::RowIterator i = d_tableau.basicRowIterator(basic); !i.atEnd(); ++i){
    const Tableau::Entry& entry = (*i);
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == basic) continue;
    const Rational& coeff =  entry.getCoefficient();
    int sgn = coeff.sgn();
    bool ub = upperBound ? (sgn > 0) : (sgn < 0);

    const DeltaRational& bound = ub ?
      d_variables.getUpperBound(nonbasic):
      d_variables.getLowerBound(nonbasic);

    DeltaRational diff = bound * coeff;
    sum = sum + diff;
  }
  return sum;
}

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational LinearEqualityModule::computeRowValue(ArithVar x, bool useSafe){
  Assert(d_tableau.isBasic(x));
  DeltaRational sum(0);

  for(Tableau::RowIterator i = d_tableau.basicRowIterator(x); !i.atEnd(); ++i){
    const Tableau::Entry& entry = (*i);
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x) continue;
    const Rational& coeff = entry.getCoefficient();

    const DeltaRational& assignment = d_variables.getAssignment(nonbasic, useSafe);
    sum = sum + (assignment * coeff);
  }
  return sum;
}

bool LinearEqualityModule::hasBounds(ArithVar basic, bool upperBound){
  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(basic); !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;

    ArithVar var = entry.getColVar();
    if(var == basic) continue;
    int sgn = entry.getCoefficient().sgn();
    if(upperBound){
      if( (sgn < 0 && !d_variables.hasLowerBound(var)) ||
          (sgn > 0 && !d_variables.hasUpperBound(var))){
        return false;
      }
    }else{
      if( (sgn < 0 && !d_variables.hasUpperBound(var)) ||
          (sgn > 0 && !d_variables.hasLowerBound(var))){
        return false;
      }
    }
  }
  return true;
}

template <bool upperBound>
void LinearEqualityModule::propagateNonbasics(ArithVar basic, Constraint c){
  Assert(d_tableau.isBasic(basic));
  Assert(c->getVariable() == basic);
  Assert(!c->assertedToTheTheory());
  Assert(!upperBound || c->isUpperBound()); // upperbound implies c is an upperbound
  Assert(upperBound || c->isLowerBound()); // !upperbound implies c is a lowerbound
  //Assert(c->canBePropagated());
  Assert(!c->hasProof());

  Debug("arith::explainNonbasics") << "LinearEqualityModule::explainNonbasics("
                                   << basic <<") start" << endl;

  vector<Constraint> bounds;

  Tableau::RowIterator iter = d_tableau.basicRowIterator(basic);
  for(; !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == basic) continue;

    const Rational& a_ij = entry.getCoefficient();

    int sgn = a_ij.sgn();
    Assert(sgn != 0);
    Constraint bound = NullConstraint;
    if(upperBound){
      if(sgn < 0){
        bound = d_variables.getLowerBoundConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_variables.getUpperBoundConstraint(nonbasic);
      }
    }else{
      if(sgn < 0){
        bound = d_variables.getUpperBoundConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_variables.getLowerBoundConstraint(nonbasic);
      }
    }
    Assert(bound != NullConstraint);
    Debug("arith::explainNonbasics") << "explainNonbasics" << bound << " for " << c << endl;
    bounds.push_back(bound);
  }
  c->impliedBy(bounds);
  Debug("arith::explainNonbasics") << "LinearEqualityModule::explainNonbasics("
                                   << basic << ") done" << endl;
}

Constraint LinearEqualityModule::weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v, const Rational& coeff, bool& anyWeakening, ArithVar basic) const {

  int sgn = coeff.sgn();
  bool ub = aboveUpper?(sgn < 0) : (sgn > 0);

  Constraint c = ub ?
    d_variables.getUpperBoundConstraint(v) :
    d_variables.getLowerBoundConstraint(v);

  bool weakened;
  do{
    const DeltaRational& bound = c->getValue();

    weakened = false;

    Constraint weaker = ub?
      c->getStrictlyWeakerUpperBound(true, true):
      c->getStrictlyWeakerLowerBound(true, true);

    if(weaker != NullConstraint){
      const DeltaRational& weakerBound = weaker->getValue();

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

        Assert(diff.sgn() > 0);
        c = weaker;
      }
    }
  }while(weakened);

  return c;
}

Node LinearEqualityModule::minimallyWeakConflict(bool aboveUpper, ArithVar basicVar) const {
  TimerStat::CodeTimer codeTimer(d_statistics.d_weakenTime);

  const DeltaRational& assignment = d_variables.getAssignment(basicVar);
  DeltaRational surplus;
  if(aboveUpper){
    Assert(d_variables.hasUpperBound(basicVar));
    Assert(assignment > d_variables.getUpperBound(basicVar));
    surplus = assignment - d_variables.getUpperBound(basicVar);
  }else{
    Assert(d_variables.hasLowerBound(basicVar));
    Assert(assignment < d_variables.getLowerBound(basicVar));
    surplus = d_variables.getLowerBound(basicVar) - assignment;
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
                  << d_variables.getAssignment(v) << " "
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

ArithVar LinearEqualityModule::minVarOrder(ArithVar x, ArithVar y) const {
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  if(x <= y){
    return x;
  } else {
    return y;
  }
}

ArithVar LinearEqualityModule::minColLength(ArithVar x, ArithVar y) const {
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!d_tableau.isBasic(x));
  Assert(!d_tableau.isBasic(y));
  uint32_t xLen = d_tableau.getColLength(x);
  uint32_t yLen = d_tableau.getColLength(y);
  if( xLen > yLen){
     return y;
  } else if( xLen== yLen ){
    return minVarOrder(x,y);
  }else{
    return x;
  }
}

ArithVar LinearEqualityModule::minRowLength(ArithVar x, ArithVar y) const {
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(d_tableau.isBasic(x));
  Assert(d_tableau.isBasic(y));
  uint32_t xLen = d_tableau.basicRowLength(x);
  uint32_t yLen = d_tableau.basicRowLength(y);
  if( xLen > yLen){
     return y;
  } else if( xLen== yLen ){
    return minVarOrder(x,y);
  }else{
    return x;
  }
}

ArithVar LinearEqualityModule::minBoundAndColLength(ArithVar x, ArithVar y) const{
  Assert(x != ARITHVAR_SENTINEL);
  Assert(y != ARITHVAR_SENTINEL);
  Assert(!d_tableau.isBasic(x));
  Assert(!d_tableau.isBasic(y));
  if(d_variables.hasEitherBound(x) && !d_variables.hasEitherBound(y)){
    return y;
  }else if(!d_variables.hasEitherBound(x) && d_variables.hasEitherBound(y)){
    return x;
  }else {
    return minColLength(x, y);
  }
}

template <bool above>
ArithVar LinearEqualityModule::selectSlack(ArithVar x_i, VarPreferenceFunction pref) const{
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
      slack = (slack == ARITHVAR_SENTINEL) ? nonbasic : (this->*pref)(slack, nonbasic);
    }
  }

  return slack;
}

const Tableau::Entry* LinearEqualityModule::selectSlackEntry(ArithVar x_i, bool above) const{
  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd();  ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = entry.getCoefficient();
    int sgn = a_ij.sgn();
    if(above && isAcceptableSlack<true>(sgn, nonbasic)){
      //If one of the above conditions is met, we have found an acceptable
      //nonbasic variable to pivot x_i with.  We can now choose which one we
      //prefer the most.
      return &entry;
    }else if(!above && isAcceptableSlack<false>(sgn, nonbasic)){
      return &entry;
    }
  }

  return NULL;
}

void LinearEqualityModule::startTrackingBoundCounts(){
  Assert(!d_areTracking);
  d_areTracking = true;
  if(Debug.isOn("arith::tracking")){
    debugCheckTracking();
  }
  Assert(d_areTracking);
}

void LinearEqualityModule::stopTrackingBoundCounts(){
  Assert(d_areTracking);
  d_areTracking = false;
  if(Debug.isOn("arith::tracking")){
    debugCheckTracking();
  }
  Assert(!d_areTracking);
}


void LinearEqualityModule::trackVariable(ArithVar x_i){
  Assert(!basicIsTracked(x_i));
  BoundCounts counts(0,0);

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd();  ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = entry.getCoefficient();
    counts += (d_variables.oldBoundCounts(nonbasic)).multiplyBySgn(a_ij.sgn());
  }
  d_boundTracking.set(x_i, counts);
}

BoundCounts LinearEqualityModule::computeBoundCounts(ArithVar x_i) const{
  BoundCounts counts(0,0);

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd();  ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    if(nonbasic == x_i) continue;

    const Rational& a_ij = entry.getCoefficient();
    counts += (d_variables.boundCounts(nonbasic)).multiplyBySgn(a_ij.sgn());
  }

  return counts;
}

// BoundCounts LinearEqualityModule::cachingCountBounds(ArithVar x_i) const{
//   if(d_boundTracking.isKey(x_i)){
//     return d_boundTracking[x_i];
//   }else{
//     return computeBoundCounts(x_i);
//   }
// }
BoundCounts LinearEqualityModule::_countBounds(ArithVar x_i) const {
  Assert(d_boundTracking.isKey(x_i));
  return d_boundTracking[x_i];
}

// BoundCounts LinearEqualityModule::countBounds(ArithVar x_i){
//   if(d_boundTracking.isKey(x_i)){
//     return d_boundTracking[x_i];
//   }else{
//     BoundCounts bc = computeBoundCounts(x_i);
//     if(d_areTracking){
//       d_boundTracking.set(x_i,bc);
//     }
//     return bc;
//   }
// }

bool LinearEqualityModule::basicsAtBounds(const UpdateInfo& u) const {
  Assert(u.describesPivot());

  ArithVar nonbasic = u.nonbasic();
  ArithVar basic = u.leaving();
  Assert(basicIsTracked(basic));
  int coeffSgn = u.getCoefficient().sgn();
  int nbdir = u.nonbasicDirection();

  Constraint c = u.limiting();
  int toUB = (c->getType() == UpperBound ||
              c->getType() == Equality) ? 1 : 0;
  int toLB = (c->getType() == LowerBound ||
              c->getType() == Equality) ? 1 : 0;


  BoundCounts bcs = d_boundTracking[basic];
  // x = c*n + \sum d*m
  // n = 1/c * x + -1/c * (\sum d*m)  
  BoundCounts nonb = bcs - d_variables.boundCounts(nonbasic).multiplyBySgn(coeffSgn);
  nonb = nonb.multiplyBySgn(-coeffSgn);
  nonb += BoundCounts(toLB, toUB).multiplyBySgn(coeffSgn);

  uint32_t length = d_tableau.basicRowLength(basic);
  Debug("basicsAtBounds")
    << "bcs " << bcs
    << "nonb " << nonb
    << "length " << length << endl;

  if(nbdir < 0){
    return bcs.atLowerBounds() + 1 == length;
  }else{
    Assert(nbdir > 0);
    return bcs.atUpperBounds() + 1 == length;
  }
}

bool LinearEqualityModule::nonbasicsAtLowerBounds(ArithVar basic) const {
  Assert(basicIsTracked(basic));
  BoundCounts bcs = d_boundTracking[basic];
  uint32_t length = d_tableau.basicRowLength(basic);

  return bcs.atLowerBounds() + 1 == length;
}

bool LinearEqualityModule::nonbasicsAtUpperBounds(ArithVar basic) const {
  Assert(basicIsTracked(basic));
  BoundCounts bcs = d_boundTracking[basic];
  uint32_t length = d_tableau.basicRowLength(basic);

  return bcs.atUpperBounds() + 1 == length;
}

void LinearEqualityModule::trackingSwap(ArithVar basic, ArithVar nb, int nbSgn) {
  Assert(basicIsTracked(basic));

  // z = a*x + \sum b*y
  // x = (1/a) z + \sum (-1/a)*b*y
  // basicCount(z) = bc(a*x) +  bc(\sum b y)
  // basicCount(x) = bc(z/a) + bc(\sum -b/a * y)

  // sgn(1/a) = sgn(a)
  // bc(a*x) = bc(x).multiply(sgn(a))
  // bc(z/a) = bc(z).multiply(sgn(a))
  // bc(\sum -b/a * y) = bc(\sum b y).multiplyBySgn(-sgn(a))
  // bc(\sum b y) = basicCount(z) - bc(a*x)
  // basicCount(x) =
  //  = bc(z).multiply(sgn(a)) + (basicCount(z) - bc(a*x)).multiplyBySgn(-sgn(a))

  BoundCounts bc = d_boundTracking[basic];
  bc -= (d_variables.boundCounts(nb)).multiplyBySgn(nbSgn);
  bc = bc.multiplyBySgn(-nbSgn);
  bc += d_variables.boundCounts(basic).multiplyBySgn(nbSgn);
  d_boundTracking.set(nb, bc);
  d_boundTracking.remove(basic);
}

void LinearEqualityModule::trackingCoefficientChange(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn){
  Assert(oldSgn != currSgn);
  BoundCounts nb_bc = d_variables.boundCounts(nb);

  if(!nb_bc.isZero()){
    ArithVar basic = d_tableau.rowIndexToBasic(ridx);
    Assert(basicIsTracked(basic));

    BoundCounts& basic_bc = d_boundTracking.get(basic);
    basic_bc.addInSgn(nb_bc, oldSgn, currSgn);
  }
}

void LinearEqualityModule::computeSafeUpdate(UpdateInfo& inf, VarPreferenceFunction pref){
  ArithVar nb = inf.nonbasic();
  int sgn = inf.nonbasicDirection();
  Assert(sgn != 0);
  Assert(!d_tableau.isBasic(nb));

  //inf.setErrorsChange(0);
  //inf.setlimiting = NullConstraint;


  // Error variables moving in the correct direction
  Assert(d_relevantErrorBuffer.empty());

  // phases :
  enum ComputeSafePhase {
    NoBoundSelected,
    NbsBoundSelected,
    BasicBoundSelected,
    DegenerateBoundSelected
  } phase;

  phase = NoBoundSelected;

  static int instance = 0;
  Debug("computeSafeUpdate") << "computeSafeUpdate " <<  (++instance) << endl;

  if(sgn > 0 && d_variables.hasUpperBound(nb)){
    Constraint ub = d_variables.getUpperBoundConstraint(nb);
    inf.updatePureFocus(ub->getValue() - d_variables.getAssignment(nb), ub);

    Assert(inf.nonbasicDelta().sgn() == sgn);
    Debug("computeSafeUpdate") << "computeSafeUpdate " <<  inf.limiting() << endl;
    phase = NbsBoundSelected;
  }else if(sgn < 0 && d_variables.hasLowerBound(nb)){
    Constraint lb = d_variables.getLowerBoundConstraint(nb);
    inf.updatePureFocus(lb->getValue() - d_variables.getAssignment(nb), lb);

    Assert(inf.nonbasicDelta().sgn() == sgn);

    Debug("computeSafeUpdate") << "computeSafeUpdate " <<  inf.limiting() << endl;
    phase = NbsBoundSelected;
  }

  Tableau::ColIterator basicIter = d_tableau.colIterator(nb);
  for(; !basicIter.atEnd(); ++basicIter){
    const Tableau::Entry& entry = *basicIter;
    Assert(entry.getColVar() == nb);

    ArithVar basic = d_tableau.rowIndexToBasic(entry.getRowIndex());
    const Rational& a_ji = entry.getCoefficient();
    int basic_movement = sgn * a_ji.sgn();

    Debug("computeSafeUpdate")
      << "computeSafeUpdate: "
      << basic << ", "
      << basic_movement << ", "
      << d_variables.cmpAssignmentUpperBound(basic) << ", "
      << d_variables.cmpAssignmentLowerBound(basic) << ", "
      << a_ji << ", "
      << d_variables.getAssignment(basic) << endl;

    Constraint proposal = NullConstraint;

    if(basic_movement > 0){
      if(d_variables.cmpAssignmentLowerBound(basic) < 0){
        d_relevantErrorBuffer.push_back(&entry);
      }
      if(d_variables.hasUpperBound(basic) &&
         d_variables.cmpAssignmentUpperBound(basic) <= 0){
        proposal = d_variables.getUpperBoundConstraint(basic);
      }
    }else if(basic_movement < 0){
      if(d_variables.cmpAssignmentUpperBound(basic) > 0){
        d_relevantErrorBuffer.push_back(&entry);
      }
      if(d_variables.hasLowerBound(basic) &&
         d_variables.cmpAssignmentLowerBound(basic) >= 0){
        proposal = d_variables.getLowerBoundConstraint(basic);
      }
    }
    if(proposal != NullConstraint){
      const Rational& coeff = entry.getCoefficient();
      DeltaRational diff = proposal->getValue() - d_variables.getAssignment(basic);
      diff /= coeff;
      int cmp = phase == NoBoundSelected ? 0 : diff.cmp(inf.nonbasicDelta());
      Assert(diff.sgn() == sgn || diff.sgn() == 0);
      bool prefer = false;
      switch(phase){
      case NoBoundSelected:
        prefer = true;
        break;
      case NbsBoundSelected:
        prefer = (sgn > 0 && cmp < 0 ) || (sgn < 0 && cmp > 0);
        break;
      case BasicBoundSelected:
        prefer =
          (sgn > 0 && cmp < 0 ) ||
          (sgn < 0 && cmp > 0) ||
          (cmp == 0 && basic == (this->*pref)(basic, inf.leaving()));
        break;
      case DegenerateBoundSelected:
        prefer = cmp == 0 && basic == (this->*pref)(basic, inf.leaving());
        break;
      }
      if(prefer){
        inf.updatePivot(diff, coeff, proposal);

        phase = (diff.sgn() != 0) ? BasicBoundSelected : DegenerateBoundSelected;
      }
    }
  }

  if(phase == DegenerateBoundSelected){
    inf.setErrorsChange(0);
  }else{
    computedFixed(inf);
  }
  inf.determineFocusDirection();

  d_relevantErrorBuffer.clear();
}

void LinearEqualityModule::computedFixed(UpdateInfo& proposal){
  Assert(proposal.nonbasicDirection() != 0);
  Assert(!d_tableau.isBasic(proposal.nonbasic()));

  //bool unconstrained = (proposal.d_limiting == NullConstraint);

  Assert(!proposal.unbounded() || !d_relevantErrorBuffer.empty());

  Assert(proposal.unbounded() ||
         proposal.nonbasicDelta().sgn() == proposal.nonbasicDirection());

  // proposal.d_value is the max

  UpdateInfo max;
  int dropped = 0;
  //Constraint maxFix = NullConstraint;
  //DeltaRational maxAmount;

  EntryPointerVector::const_iterator i = d_relevantErrorBuffer.begin();
  EntryPointerVector::const_iterator i_end = d_relevantErrorBuffer.end();
  for(; i != i_end; ++i){
    const Tableau::Entry& entry = *(*i);
    Assert(entry.getColVar() == proposal.nonbasic());

    ArithVar basic = d_tableau.rowIndexToBasic(entry.getRowIndex());
    const Rational& a_ji = entry.getCoefficient();
    int basic_movement = proposal.nonbasicDirection() * a_ji.sgn();

    DeltaRational theta;
    DeltaRational proposedValue;
    if(!proposal.unbounded()){
      theta = proposal.nonbasicDelta() * a_ji;
      proposedValue = theta + d_variables.getAssignment(basic);
    }

    Constraint fixed = NullConstraint;

    if(basic_movement < 0){
      Assert(d_variables.cmpAssignmentUpperBound(basic) > 0);

      if(proposal.unbounded() || d_variables.cmpToUpperBound(basic, proposedValue) <= 0){
        --dropped;
        fixed = d_variables.getUpperBoundConstraint(basic);
      }
    }else if(basic_movement > 0){
      Assert(d_variables.cmpAssignmentLowerBound(basic) < 0);

      if(proposal.unbounded() || d_variables.cmpToLowerBound(basic, proposedValue) >= 0){
        --dropped;
        fixed = d_variables.getLowerBoundConstraint(basic);
      }
    }
    if(fixed != NullConstraint){
      DeltaRational amount = fixed->getValue() - d_variables.getAssignment(basic);
      amount /= a_ji;
      Assert(amount.sgn() == proposal.nonbasicDirection());

      if(max.uninitialized()){
        max = UpdateInfo(proposal.nonbasic(), proposal.nonbasicDirection());
        max.updatePivot(amount, a_ji, fixed, dropped);
      }else{
        int cmp = amount.cmp(max.nonbasicDelta());
        bool prefer =
          (proposal.nonbasicDirection() < 0 && cmp < 0) ||
          (proposal.nonbasicDirection() > 0 && cmp > 0) ||
          (cmp == 0 && fixed->getVariable() < max.limiting()->getVariable());

        if(prefer){
          max.updatePivot(amount, a_ji, fixed, dropped);
        }else{
          max.setErrorsChange(dropped);
        }
      }
    }
  }
  Assert(dropped < 0 || !proposal.unbounded());

  if(dropped < 0){
    proposal = max;
  }else{
    Assert(dropped == 0);
    Assert(proposal.nonbasicDelta().sgn() != 0);
    Assert(proposal.nonbasicDirection() != 0);
    proposal.setErrorsChange(0);
  }
  Assert(proposal.errorsChange() == dropped);
}

ArithVar LinearEqualityModule::minBy(const ArithVarVec& vec, VarPreferenceFunction pf) const{
  if(vec.empty()) {
    return ARITHVAR_SENTINEL;
  }else {
    ArithVar sel = vec.front();
    ArithVarVec::const_iterator i = vec.begin() + 1;
    ArithVarVec::const_iterator i_end = vec.end();
    for(; i != i_end; ++i){
      sel = (this->*pf)(sel, *i);
    }
    return sel;
  }
}

bool LinearEqualityModule::accumulateBorder(const Tableau::Entry& entry, bool ub){
  ArithVar currBasic = d_tableau.rowIndexToBasic(entry.getRowIndex());

  Assert(basicIsTracked(currBasic));

  Constraint bound = ub ?
    d_variables.getUpperBoundConstraint(currBasic):
    d_variables.getLowerBoundConstraint(currBasic);

  if(bound == NullConstraint){ return false; }
  Assert(bound != NullConstraint);

  const Rational& coeff = entry.getCoefficient();

  const DeltaRational& assignment = d_variables.getAssignment(currBasic);
  DeltaRational toBound = bound->getValue() - assignment;
  DeltaRational nbDiff = toBound/coeff;

  // if ub
  // if toUB >= 0
  // then ub >= currBasic
  //   if sgn > 0,
  //   then diff >= 0, so nb must increase for G
  //   else diff <= 0, so nb must decrease for G
  // else ub < currBasic
  //   if sgn > 0,
  //   then diff < 0, so nb must decrease for G
  //   else diff > 0, so nb must increase for G

  int diffSgn = nbDiff.sgn();

  if(diffSgn != 0 && willBeInConflictAfterPivot(entry, nbDiff, ub)){
    return true;
  }else{
    bool areFixing = ub ? (toBound.sgn() < 0 ) : (toBound.sgn() > 0);
    Border border(bound, nbDiff, areFixing, &entry, ub);
    bool increasing =
      (diffSgn > 0) ||
      (diffSgn == 0 && ((coeff.sgn() > 0) == ub));

    // assume diffSgn == 0
    // if coeff > 0,
    //   if ub, inc
    //   else, dec
    // else coeff < 0
    //   if ub, dec
    //   else, inc

    if(increasing){
      Debug("handleBorders") << "push back increasing " << border << endl;
      d_increasing.push_back(border);
    }else{
      Debug("handleBorders") << "push back decreasing " << border << endl;
      d_decreasing.push_back(border);
    }
    return false;
  }
}

bool LinearEqualityModule::willBeInConflictAfterPivot(const Tableau::Entry& entry, const DeltaRational& nbDiff, bool bToUB) const{
  int nbSgn = nbDiff.sgn();
  Assert(nbSgn != 0);

  if(nbSgn > 0){
    if(d_upperBoundDifference.nothing() || nbDiff <= d_upperBoundDifference){
      return false;
    }
  }else{
    if(d_lowerBoundDifference.nothing() || nbDiff >= d_lowerBoundDifference){
      return false;
    }
  }

  // Assume past this point, nb will be in error if this pivot is done
  ArithVar nb = entry.getColVar();
  ArithVar basic = d_tableau.rowIndexToBasic(entry.getRowIndex());
  Assert(basicIsTracked(basic));
  int coeffSgn = entry.getCoefficient().sgn();


  // if bToUB, then basic is going to be set to its upperbound
  // if not bToUB, then basic is going to be set to its lowerbound

  // Different steps of solving for this:
  // 1) y = a * x + \sum b * z
  // 2) -a * x = -y + \sum b * z
  // 3) x = (-1/a) * ( -y + \sum b * z)

  Assert(basicIsTracked(basic));
  BoundCounts bc = d_boundTracking[basic];

  // 1) y = a * x + \sum b * z
  // Get bc(\sum b * z)
  BoundCounts sumOnly = bc - d_variables.boundCounts(nb).multiplyBySgn(coeffSgn);

  // y's bounds in the proposed model
  int yWillBeAtUb = (bToUB || d_variables.boundsAreEqual(basic)) ? 1 : 0;
  int yWillBeAtLb = (!bToUB || d_variables.boundsAreEqual(basic)) ? 1 : 0;
  BoundCounts ysBounds(yWillBeAtLb, yWillBeAtUb);

  // 2) -a * x = -y + \sum b * z
  // Get bc(-y + \sum b * z)
  BoundCounts withNegY = sumOnly + ysBounds.multiplyBySgn(-1);

  // 3) x = (-1/a) * ( -y + \sum b * z)
  // Get bc((-1/a) * ( -y + \sum b * z))
  BoundCounts xsBoundsAfterPivot = withNegY.multiplyBySgn(-coeffSgn);

  uint32_t length = d_tableau.basicRowLength(basic);
  if(nbSgn > 0){
    // Only check for the upper bound being violated
    return xsBoundsAfterPivot.atLowerBounds() + 1 == length;
  }else{
    // Only check for the lower bound being violated
    return xsBoundsAfterPivot.atUpperBounds() + 1 == length;
  }
}

UpdateInfo LinearEqualityModule::mkConflictUpdate(const Tableau::Entry& entry, bool ub) const{
  ArithVar currBasic = d_tableau.rowIndexToBasic(entry.getRowIndex());
  ArithVar nb = entry.getColVar();

  Constraint bound = ub ?
    d_variables.getUpperBoundConstraint(currBasic):
    d_variables.getLowerBoundConstraint(currBasic);


  const Rational& coeff = entry.getCoefficient();
  const DeltaRational& assignment = d_variables.getAssignment(currBasic);
  DeltaRational toBound = bound->getValue() - assignment;
  DeltaRational nbDiff = toBound/coeff;

  return UpdateInfo::conflict(nb, nbDiff, coeff, bound);
}

UpdateInfo LinearEqualityModule::speculativeUpdate(ArithVar nb, const Rational& focusCoeff, UpdatePreferenceFunction pref){
  Assert(d_increasing.empty());
  Assert(d_decreasing.empty());
  Assert(d_lowerBoundDifference.nothing());
  Assert(d_upperBoundDifference.nothing());

  int focusCoeffSgn = focusCoeff.sgn();

  static int instance = 0;
  ++instance;
  Debug("speculativeUpdate") << "speculativeUpdate " << instance << endl;
  Debug("speculativeUpdate") << "nb " << nb << endl;
  Debug("speculativeUpdate") << "focusCoeff " << focusCoeff << endl;

  if(d_variables.hasUpperBound(nb)){
    Constraint ub = d_variables.getUpperBoundConstraint(nb);
    d_upperBoundDifference = ub->getValue() - d_variables.getAssignment(nb);
    Border border(ub, d_upperBoundDifference, false, NULL, true);
    Debug("handleBorders") << "push back increasing " << border << endl;
    d_increasing.push_back(border);
  }
  if(d_variables.hasLowerBound(nb)){
    Constraint lb = d_variables.getLowerBoundConstraint(nb);
    d_lowerBoundDifference = lb->getValue() - d_variables.getAssignment(nb);
    Border border(lb, d_lowerBoundDifference, false, NULL, false);
    Debug("handleBorders") << "push back decreasing " << border << endl;
    d_decreasing.push_back(border);
  }

  Tableau::ColIterator colIter = d_tableau.colIterator(nb);
  for(; !colIter.atEnd(); ++colIter){
    const Tableau::Entry& entry = *colIter;
    Assert(entry.getColVar() == nb);

    if(accumulateBorder(entry, true)){
      clearSpeculative();
      return mkConflictUpdate(entry, true);
    }
    if(accumulateBorder(entry, false)){
      clearSpeculative();
      return mkConflictUpdate(entry, false);
    }
  }

  UpdateInfo selected;
  BorderHeap& withSgn = focusCoeffSgn > 0 ? d_increasing : d_decreasing;
  BorderHeap& againstSgn = focusCoeffSgn > 0 ? d_decreasing : d_increasing;

  handleBorders(selected, nb, focusCoeff, withSgn, 0, pref);
  int m = 1 - selected.errorsChangeSafe(0);
  handleBorders(selected, nb, focusCoeff, againstSgn, m, pref);

  clearSpeculative();
  return selected;
}

void LinearEqualityModule::clearSpeculative(){
  // clear everything away
  d_increasing.clear();
  d_decreasing.clear();
  d_lowerBoundDifference.clear();
  d_upperBoundDifference.clear();
}

void LinearEqualityModule::handleBorders(UpdateInfo& selected, ArithVar nb, const Rational& focusCoeff, BorderHeap& heap, int minimumFixes, UpdatePreferenceFunction pref){
  Assert(minimumFixes >= 0);

  // The values popped off of the heap
  // should be popped with the values closest to 0
  // being first and larger in absolute value last


  int fixesRemaining = heap.possibleFixes();

  Debug("handleBorders")
    << "handleBorders "
    << "nb " << nb
    << "fc " << focusCoeff
    << "h.e " << heap.empty()
    << "h.dir " << heap.direction()
    << "h.rem " << fixesRemaining
    << "h.0s " << heap.numZeroes()
    << "min " << minimumFixes
    << endl;

  if(heap.empty()){
    // if the heap is empty, return
    return;
  }

  bool zeroesWillDominate = fixesRemaining - heap.numZeroes() < minimumFixes;

  // can the number of fixes ever exceed the minimum?
  // no more than the number of possible fixes can be fixed in total
  // nothing can be fixed before the zeroes are taken care of
  if(minimumFixes > 0 && zeroesWillDominate){
    return;
  }


  int negErrorChange = 0;
  int nbDir = heap.direction();

  // points at the beginning of the heap
  if(zeroesWillDominate){
    heap.dropNonZeroes();
  }
  heap.make_heap();


  // pretend like the previous block had a value of zero.
  // The block that actually has a value of 0 must handle this.
  const DeltaRational zero(0);
  const DeltaRational* prevBlockValue = &zero;

  /** The coefficient changes as the value crosses border. */
  Rational effectiveCoefficient = focusCoeff;

  /* Keeps track of the change to the value of the focus function.*/
  DeltaRational totalFocusChange(0);

  const int focusCoeffSgn = focusCoeff.sgn();

  while(heap.more()  &&
        (fixesRemaining + negErrorChange > minimumFixes ||
         (fixesRemaining + negErrorChange == minimumFixes &&
          effectiveCoefficient.sgn() == focusCoeffSgn))){
    // There are more elements &&
    // we can either fix at least 1 more variable in the error function
    // or we can improve the error function


    int brokenInBlock = 0;
    BorderVec::const_iterator endBlock = heap.end();

    pop_block(heap, brokenInBlock, fixesRemaining, negErrorChange);

    // if endVec == beginVec, block starts there
    // other wise, block starts at endVec
    BorderVec::const_iterator startBlock
      = heap.more() ? heap.end() : heap.begin();

    const DeltaRational& blockValue = (*startBlock).d_diff;

    // if decreasing
    // blockValue < prevBlockValue
    // diff.sgn() = -1
    DeltaRational diff = blockValue - (*prevBlockValue);
    DeltaRational blockChangeToFocus =  diff * effectiveCoefficient;
    totalFocusChange += blockChangeToFocus;

    Debug("handleBorders")
      << "blockValue " << (blockValue)
      << "diff " << diff
      << "blockChangeToFocus " << totalFocusChange
      << "blockChangeToFocus " << totalFocusChange
      << "negErrorChange " << negErrorChange
      << "brokenInBlock " << brokenInBlock
      << "fixesRemaining " << fixesRemaining
      << endl;

    int currFocusChangeSgn = totalFocusChange.sgn();
    for(BorderVec::const_iterator i = startBlock; i != endBlock; ++i){
      const Border& b = *i;

      Debug("handleBorders") << b << endl;

      bool makesImprovement = negErrorChange > 0 ||
        (negErrorChange == 0  && currFocusChangeSgn > 0);

      if(!makesImprovement){
        if(b.ownBorder() || minimumFixes > 0){
          continue;
        }
      }

      UpdateInfo proposal(nb, nbDir);
      if(b.ownBorder()){
        proposal.witnessedUpdate(b.d_diff, b.d_bound, -negErrorChange, currFocusChangeSgn);
      }else{
        proposal.update(b.d_diff, b.getCoefficient(), b.d_bound, -negErrorChange, currFocusChangeSgn);
      }

      if(selected.unbounded() || (this->*pref)(selected, proposal)){
        selected = proposal;
      }
    }

    effectiveCoefficient += updateCoefficient(startBlock, endBlock);
    prevBlockValue = &blockValue;
    negErrorChange -= brokenInBlock;
  }
}

Rational LinearEqualityModule::updateCoefficient(BorderVec::const_iterator startBlock, BorderVec::const_iterator endBlock){
  //update coefficient
  Rational changeToCoefficient(0);
  for(BorderVec::const_iterator i = startBlock; i != endBlock; ++i){
    const Border& curr = *i;
    if(curr.ownBorder()){// breaking its own bound
      if(curr.d_upperbound){
        changeToCoefficient -= 1;
      }else{
        changeToCoefficient += 1;
      }
    }else{
      const Rational& coeff = curr.d_entry->getCoefficient();
      if(curr.d_areFixing){
        if(curr.d_upperbound){// fixing an upper bound
          changeToCoefficient += coeff;
        }else{// fixing a lower bound
          changeToCoefficient -= coeff;
        }
      }else{
        if(curr.d_upperbound){// breaking an upper bound
          changeToCoefficient -= coeff;
        }else{
          // breaking a lower bound
          changeToCoefficient += coeff;
        }
      }
    }
  }
  return changeToCoefficient;
}

void LinearEqualityModule::pop_block(BorderHeap& heap, int& brokenInBlock, int& fixesRemaining, int& negErrorChange){
  Assert(heap.more());

  if(heap.top().d_areFixing){
    fixesRemaining--;
    negErrorChange++;
  }else{
    brokenInBlock++;
  }
  heap.pop_heap();
  const DeltaRational& blockValue = (*heap.end()).d_diff;

  while(heap.more()){
    const Border& top = heap.top();
    if(blockValue == top.d_diff){
      // belongs to the block
      if(top.d_areFixing){
        fixesRemaining--;
        negErrorChange++;
      }else{
        brokenInBlock++;
      }
      heap.pop_heap();
    }else{
      // does not belong to the block
      Assert((heap.direction() > 0) ?
             (blockValue < top.d_diff) : (blockValue > top.d_diff));
      break;
    }
  }
}

void LinearEqualityModule::substitutePlusTimesConstant(ArithVar to, ArithVar from, const Rational& mult){
  d_tableau.substitutePlusTimesConstant(to, from, mult, d_trackCallback);
}
void LinearEqualityModule::directlyAddToCoefficient(ArithVar row, ArithVar col, const Rational& mult){
  d_tableau.directlyAddToCoefficient(row, col, mult, d_trackCallback);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
