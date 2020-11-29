/*********************                                                        */
/*! \file linear_equality.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This implements the LinearEqualityModule.
 **
 ** This implements the LinearEqualityModule.
 **/
#include "theory/arith/linear_equality.h"

#include "base/output.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/constraint.h"


using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

/* Explicitly instatiate these functions. */

template ArithVar LinearEqualityModule::selectSlack<true>(ArithVar x_i, VarPreferenceFunction pf) const;
template ArithVar LinearEqualityModule::selectSlack<false>(ArithVar x_i, VarPreferenceFunction pf) const;

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

LinearEqualityModule::LinearEqualityModule(ArithVariables& vars, Tableau& t, BoundInfoMap& boundsTracking, BasicVarModelUpdateCallBack f):
  d_variables(vars),
  d_tableau(t),
  d_basicVariableUpdates(f),
  d_increasing(1),
  d_decreasing(-1),
  d_upperBoundDifference(),
  d_lowerBoundDifference(),
  d_one(1),
  d_negOne(-1),
  d_btracking(boundsTracking),
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
  d_weakenTime("theory::arith::weakening::time"),
  d_forceTime("theory::arith::forcing::time")
{
  smtStatisticsRegistry()->registerStat(&d_statPivots);
  smtStatisticsRegistry()->registerStat(&d_statUpdates);

  smtStatisticsRegistry()->registerStat(&d_pivotTime);
  smtStatisticsRegistry()->registerStat(&d_adjTime);

  smtStatisticsRegistry()->registerStat(&d_weakeningAttempts);
  smtStatisticsRegistry()->registerStat(&d_weakeningSuccesses);
  smtStatisticsRegistry()->registerStat(&d_weakenings);
  smtStatisticsRegistry()->registerStat(&d_weakenTime);
  smtStatisticsRegistry()->registerStat(&d_forceTime);
}

LinearEqualityModule::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_statPivots);
  smtStatisticsRegistry()->unregisterStat(&d_statUpdates);
  smtStatisticsRegistry()->unregisterStat(&d_pivotTime);
  smtStatisticsRegistry()->unregisterStat(&d_adjTime);


  smtStatisticsRegistry()->unregisterStat(&d_weakeningAttempts);
  smtStatisticsRegistry()->unregisterStat(&d_weakeningSuccesses);
  smtStatisticsRegistry()->unregisterStat(&d_weakenings);
  smtStatisticsRegistry()->unregisterStat(&d_weakenTime);
  smtStatisticsRegistry()->unregisterStat(&d_forceTime);
}

void LinearEqualityModule::includeBoundUpdate(ArithVar v, const BoundsInfo& prev){
  Assert(!d_areTracking);

  BoundsInfo curr = d_variables.boundsInfo(v);

  Assert(prev != curr);
  Tableau::ColIterator basicIter = d_tableau.colIterator(v);
  for(; !basicIter.atEnd(); ++basicIter){
    const Tableau::Entry& entry = *basicIter;
    Assert(entry.getColVar() == v);
    int a_ijSgn = entry.getCoefficient().sgn();

    RowIndex ridx = entry.getRowIndex();
    BoundsInfo& counts = d_btracking.get(ridx);
    Debug("includeBoundUpdate") << d_tableau.rowIndexToBasic(ridx) << " " << counts << " to " ;
    counts.addInChange(a_ijSgn, prev, curr);
    Debug("includeBoundUpdate") << counts << " " << a_ijSgn << std::endl;
  }
}

void LinearEqualityModule::updateMany(const DenseMap<DeltaRational>& many){
  for(DenseMap<DeltaRational>::const_iterator i = many.begin(), i_end = many.end(); i != i_end; ++i){
    ArithVar nb = *i;
    if(!d_tableau.isBasic(nb)){
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
}




void LinearEqualityModule::applySolution(const DenseSet& newBasis, const DenseMap<DeltaRational>& newValues){
  forceNewBasis(newBasis);
  updateMany(newValues);
}

void LinearEqualityModule::forceNewBasis(const DenseSet& newBasis){
  TimerStat::CodeTimer codeTimer(d_statistics.d_forceTime);
  cout << "force begin" << endl;
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
    Message() << toRemove << " " << toAdd << endl;
    d_tableau.pivot(toRemove, toAdd, d_trackCallback);
    d_basicVariableUpdates(toAdd);

    Trace("arith::forceNewBasis") << needsToBeAdded.size() << "to go" << endl;
    Message() << needsToBeAdded.size() << "to go" << endl;
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


  BoundCounts before = d_variables.atBoundCounts(x_i);
  d_variables.setAssignment(x_i, v);
  BoundCounts after = d_variables.atBoundCounts(x_i);

  bool anyChange = before != after;

  Tableau::ColIterator colIter = d_tableau.colIterator(x_i);
  for(; !colIter.atEnd(); ++colIter){
    const Tableau::Entry& entry = *colIter;
    Assert(entry.getColVar() == x_i);

    RowIndex ridx = entry.getRowIndex();
    ArithVar x_j = d_tableau.rowIndexToBasic(ridx);
    const Rational& a_ji = entry.getCoefficient();

    const DeltaRational& assignment = d_variables.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    Debug("update") << x_j << " " << a_ji << assignment << " -> " << nAssignment << endl;
    BoundCounts xjBefore = d_variables.atBoundCounts(x_j);
    d_variables.setAssignment(x_j, nAssignment);
    BoundCounts xjAfter = d_variables.atBoundCounts(x_j);

    Assert(rowIndexIsTracked(ridx));
    BoundsInfo& next_bc_k = d_btracking.get(ridx);
    if(anyChange){
      next_bc_k.addInAtBoundChange(a_ji.sgn(), before, after);
    }
    if(xjBefore != xjAfter){
      next_bc_k.addInAtBoundChange(-1, xjBefore, xjAfter);
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
      Debug("arith::tracking") << var << " " << d_variables.boundsInfo(var)
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
      RowIndex ridx = d_tableau.basicToRowIndex(basic);
      BoundsInfo computed = computeRowBoundInfo(ridx, false);
      Debug("arith::tracking")
        << "computed " << computed
        << " tracking " << d_btracking[ridx] << endl;
      Assert(computed == d_btracking[ridx]);
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

DeltaRational LinearEqualityModule::computeRowBound(RowIndex ridx, bool rowUb, ArithVar skip) const {
  DeltaRational sum(0,0);
  for(Tableau::RowIterator i = d_tableau.ridRowIterator(ridx); !i.atEnd(); ++i){
    const Tableau::Entry& entry = (*i);
    ArithVar v = entry.getColVar();
    if(v == skip){ continue; }

    const Rational& coeff =  entry.getCoefficient();
    bool vUb = (rowUb == (coeff.sgn() > 0));

    const DeltaRational& bound = vUb ?
      d_variables.getUpperBound(v):
      d_variables.getLowerBound(v);

    DeltaRational diff = bound * coeff;
    sum = sum + diff;
  }
  return sum;
}

/**
 * Computes the value of a basic variable using the current assignment.
 */
DeltaRational LinearEqualityModule::computeRowValue(ArithVar x, bool useSafe) const{
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

const Tableau::Entry* LinearEqualityModule::rowLacksBound(RowIndex ridx, bool rowUb, ArithVar skip){
  Tableau::RowIterator iter = d_tableau.ridRowIterator(ridx);
  for(; !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;

    ArithVar var = entry.getColVar();
    if(var == skip) { continue; }

    int sgn = entry.getCoefficient().sgn();
    bool selectUb = (rowUb == (sgn > 0));
    bool hasBound = selectUb ?
      d_variables.hasUpperBound(var):
      d_variables.hasLowerBound(var);
    if(!hasBound){
      return &entry;
    }
  }
  return NULL;
}

void LinearEqualityModule::propagateBasicFromRow(ConstraintP c){
  Assert(c != NullConstraint);
  Assert(c->isUpperBound() || c->isLowerBound());
  Assert(!c->assertedToTheTheory());
  Assert(!c->hasProof());

  bool upperBound = c->isUpperBound();
  ArithVar basic = c->getVariable();
  RowIndex ridx = d_tableau.basicToRowIndex(basic);

  ConstraintCPVec bounds;
  RationalVectorP coeffs = ARITH_NULLPROOF(new RationalVector());
  propagateRow(bounds, ridx, upperBound, c, coeffs);
  c->impliedByFarkas(bounds, coeffs, false);
  c->tryToPropagate();

  if(coeffs != RationalVectorPSentinel) { delete coeffs; }
}

/* An explanation of the farkas coefficients.
 *
 * We are proving c using the other variables on the row.
 * The proof is in terms of the other constraints and the negation of c, ~c.
 *
 * A row has the form:
 *   sum a_i * x_i  = 0
 * or
 *   sx + sum r y + sum q z = 0
 * where r > 0 and q < 0.
 *
 * If rowUp, we are proving c
 *   g = sum r u_y + sum q l_z
 *   and c is entailed by -sx <= g
 * If !rowUp, we are proving c
 *   g = sum r l_y + sum q u_z
 *   and c is entailed by -sx >= g
 *
 *             | s     | c         | ~c       | u_i     | l_i
 *   if  rowUp | s > 0 | x >= -g/s | x < -g/s | a_i > 0 | a_i < 0
 *   if  rowUp | s < 0 | x <= -g/s | x > -g/s | a_i > 0 | a_i < 0
 *   if !rowUp | s > 0 | x <= -g/s | x > -g/s | a_i < 0 | a_i > 0
 *   if !rowUp | s < 0 | x >= -g/s | x < -g/s | a_i < 0 | a_i > 0
 *
 *
 * Thus we treat !rowUp as multiplying the row by -1 and rowUp as 1
 * for the entire row.
 */
void LinearEqualityModule::propagateRow(ConstraintCPVec& into, RowIndex ridx, bool rowUp, ConstraintP c, RationalVectorP farkas){
  Assert(!c->assertedToTheTheory());
  Assert(c->canBePropagated());
  Assert(!c->hasProof());

  if(farkas != RationalVectorPSentinel){
    Assert(farkas->empty());
    farkas->push_back(Rational(0));
  }

  ArithVar v = c->getVariable();
  Debug("arith::propagateRow") << "LinearEqualityModule::propagateRow("
                                   << ridx << ", " << rowUp << ", " << v << ") start" << endl;

  const Rational& multiple = rowUp ? d_one : d_negOne;

  Debug("arith::propagateRow") << "multiple: " << multiple << endl;

  Tableau::RowIterator iter = d_tableau.ridRowIterator(ridx);
  for(; !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar nonbasic = entry.getColVar();
    const Rational& a_ij = entry.getCoefficient();
    int sgn = a_ij.sgn();
    Assert(sgn != 0);
    bool selectUb = rowUp ? (sgn > 0) : (sgn < 0);

    Assert(nonbasic != v || (rowUp && a_ij.sgn() > 0 && c->isLowerBound())
           || (rowUp && a_ij.sgn() < 0 && c->isUpperBound())
           || (!rowUp && a_ij.sgn() > 0 && c->isUpperBound())
           || (!rowUp && a_ij.sgn() < 0 && c->isLowerBound()));

    if(Debug.isOn("arith::propagateRow")){
      if(nonbasic == v){
        Debug("arith::propagateRow") << "(target) "
                                     << rowUp << " "
                                     << a_ij.sgn() << " "
                                     << c->isLowerBound() << " "
                                     << c->isUpperBound() << endl;

        Debug("arith::propagateRow") << "(target) ";
      }
      Debug("arith::propagateRow") << "propagateRow " << a_ij << " * " << nonbasic ;
    }

    if(nonbasic == v){
      if(farkas != RationalVectorPSentinel){
        Assert(farkas->front().isZero());
        Rational multAij = multiple * a_ij;
        Debug("arith::propagateRow") << "(" << multAij << ") ";
        farkas->front() = multAij;
      }

      Debug("arith::propagateRow") << c << endl;
    }else{

      ConstraintCP bound = selectUb
        ? d_variables.getUpperBoundConstraint(nonbasic)
        : d_variables.getLowerBoundConstraint(nonbasic);

      if(farkas != RationalVectorPSentinel){
        Rational multAij = multiple * a_ij;
        Debug("arith::propagateRow") << "(" << multAij << ") ";
        farkas->push_back(multAij);
      }
      Assert(bound != NullConstraint);
      Debug("arith::propagateRow") << bound << endl;
      into.push_back(bound);
    }
  }
  Debug("arith::propagateRow") << "LinearEqualityModule::propagateRow("
                                   << ridx << ", " << rowUp << ", " << v << ") done" << endl;

}

ConstraintP LinearEqualityModule::weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v, const Rational& coeff, bool& anyWeakening, ArithVar basic) const {

  int sgn = coeff.sgn();
  bool ub = aboveUpper?(sgn < 0) : (sgn > 0);

  ConstraintP c = ub ?
    d_variables.getUpperBoundConstraint(v) :
    d_variables.getLowerBoundConstraint(v);

  bool weakened;
  do{
    const DeltaRational& bound = c->getValue();

    weakened = false;

    ConstraintP weaker = ub?
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

        Debug("arith::weak") << "found:" << endl;
        if(v == basic){
          Debug("arith::weak") << "  basic: ";
        }
        Debug("arith::weak") << "  " << surplus << " "<< diff  << endl
                             << "  " << bound << c << endl
                             << "  " << weakerBound << weaker << endl;

        Assert(diff.sgn() > 0);
        c = weaker;
      }
    }
  }while(weakened);

  return c;
}

/* An explanation of the farkas coefficients.
 *
 * We are proving a conflict on the basic variable x_b.
 * If aboveUpper, then the conflict is with the constraint c : x_b <= u_b.
 * If !aboveUpper, then the conflict is with the constraint c : x_b >= l_b.
 *
 * A row has the form:
 *   -x_b sum a_i * x_i  = 0
 * or
 *   -x_b + sum r y + sum q z = 0,
 *    x_b = sum r y + sum q z
 * where r > 0 and q < 0.
 *
 *
 * If !aboveUp, we are proving ~c: x_b < l_b
 *   g = sum r u_y + sum q l_z
 *   x_b <= g < l_b
 *   and ~c is entailed by x_b <= g
 *
 * If aboveUp, we are proving ~c : x_b > u_b
 *   g = sum r l_y + sum q u_z
 *   x_b >= g > u_b
 *   and ~c is entailed by x_b >= g
 *
 *
 *               | s     | c         | ~c       | u_i     | l_i
 *   if !aboveUp | s > 0 | x >= -g/s | x < -g/s | a_i > 0 | a_i < 0
 *   if !aboveUp | s < 0 | x <= -g/s | x > -g/s | a_i > 0 | a_i < 0
 *   if  aboveUp | s > 0 | x <= -g/s | x > -g/s | a_i < 0 | a_i > 0
 *   if  aboveUp | s < 0 | x >= -g/s | x < -g/s | a_i < 0 | a_i > 0
 *
 * Thus we treat aboveUp as multiplying the row by -1 and !aboveUp as 1
 * for the entire row.
 */
ConstraintCP LinearEqualityModule::minimallyWeakConflict(bool aboveUpper, ArithVar basicVar, FarkasConflictBuilder& fcs) const {
  Assert(!fcs.underConstruction());
  TimerStat::CodeTimer codeTimer(d_statistics.d_weakenTime);

  Debug("arith::weak") << "LinearEqualityModule::minimallyWeakConflict("
                       << aboveUpper <<", "<< basicVar << ", ...) start" << endl;

  const Rational& adjustSgn = aboveUpper ? d_negOne : d_one;
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

  bool anyWeakenings = false;
  for(Tableau::RowIterator i = d_tableau.basicRowIterator(basicVar); !i.atEnd(); ++i){
    const Tableau::Entry& entry = *i;
    ArithVar v = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    bool weakening = false;
    ConstraintP c = weakestExplanation(aboveUpper, surplus, v, coeff, weakening, basicVar);
    Debug("arith::weak") << "weak : " << weakening << " "
                         << c->assertedToTheTheory() << " "
                         << d_variables.getAssignment(v) << " "
                         << c << endl;
    anyWeakenings = anyWeakenings || weakening;

    fcs.addConstraint(c, coeff, adjustSgn);
    if(basicVar == v){
      Assert(!c->negationHasProof());
      fcs.makeLastConsequent();
    }
  }
  Assert(fcs.consequentIsSet());

  ConstraintCP conflicted = fcs.commitConflict();

  ++d_statistics.d_weakeningAttempts;
  if(anyWeakenings){
    ++d_statistics.d_weakeningSuccesses;
  }
  Debug("arith::weak") << "LinearEqualityModule::minimallyWeakConflict("
                       << aboveUpper <<", "<< basicVar << ", ...) done" << endl;
  return conflicted;
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


void LinearEqualityModule::trackRowIndex(RowIndex ridx){
  Assert(!rowIndexIsTracked(ridx));
  BoundsInfo bi = computeRowBoundInfo(ridx, true);
  d_btracking.set(ridx, bi);
}

BoundsInfo LinearEqualityModule::computeRowBoundInfo(RowIndex ridx, bool inQueue) const{
  BoundsInfo bi;

  Tableau::RowIterator iter = d_tableau.ridRowIterator(ridx);
  for(; !iter.atEnd();  ++iter){
    const Tableau::Entry& entry = *iter;
    ArithVar v = entry.getColVar();
    const Rational& a_ij = entry.getCoefficient();
    bi += (d_variables.selectBoundsInfo(v, inQueue)).multiplyBySgn(a_ij.sgn());
  }
  return bi;
}

BoundCounts LinearEqualityModule::debugBasicAtBoundCount(ArithVar x_i) const {
  return d_btracking[d_tableau.basicToRowIndex(x_i)].atBounds();
}

/**
 * If the pivot described in u were performed,
 * then the row would qualify as being either at the minimum/maximum
 * to the non-basics being at their bounds.
 * The minimum/maximum is determined by the direction the non-basic is changing.
 */
bool LinearEqualityModule::basicsAtBounds(const UpdateInfo& u) const {
  Assert(u.describesPivot());

  ArithVar nonbasic = u.nonbasic();
  ArithVar basic = u.leaving();
  Assert(basicIsTracked(basic));
  int coeffSgn = u.getCoefficient().sgn();
  int nbdir = u.nonbasicDirection();

  ConstraintP c = u.limiting();
  int toUB = (c->getType() == UpperBound ||
              c->getType() == Equality) ? 1 : 0;
  int toLB = (c->getType() == LowerBound ||
              c->getType() == Equality) ? 1 : 0;

  RowIndex ridx = d_tableau.basicToRowIndex(basic);

  BoundCounts bcs = d_btracking[ridx].atBounds();
  // x = c*n + \sum d*m
  // 0 = -x + c*n + \sum d*m
  // n = 1/c * x + -1/c * (\sum d*m)
  BoundCounts nonb = bcs - d_variables.atBoundCounts(nonbasic).multiplyBySgn(coeffSgn);
  nonb.addInChange(-1, d_variables.atBoundCounts(basic), BoundCounts(toLB, toUB));
  nonb = nonb.multiplyBySgn(-coeffSgn);

  uint32_t length = d_tableau.basicRowLength(basic);
  Debug("basicsAtBounds")
    << "bcs " << bcs
    << "nonb " << nonb
    << "length " << length << endl;
  // nonb has nb excluded.
  if(nbdir < 0){
    return nonb.lowerBoundCount() + 1 == length;
  }else{
    Assert(nbdir > 0);
    return nonb.upperBoundCount() + 1 == length;
  }
}

bool LinearEqualityModule::nonbasicsAtLowerBounds(ArithVar basic) const {
  Assert(basicIsTracked(basic));
  RowIndex ridx = d_tableau.basicToRowIndex(basic);

  BoundCounts bcs = d_btracking[ridx].atBounds();
  uint32_t length = d_tableau.basicRowLength(basic);

  // return true if excluding the basic is every element is at its "lowerbound"
  // The psuedo code is:
  //   bcs -= basic.count(basic, basic's sgn)
  //   return bcs.lowerBoundCount() + 1 == length
  // As basic's sign is always -1, we can pull out the pieces of the count:
  //   bcs.lowerBoundCount() - basic.atUpperBoundInd() + 1 == length
  // basic.atUpperBoundInd() is either 0 or 1
  uint32_t lbc = bcs.lowerBoundCount();
  return  (lbc == length) ||
    (lbc + 1 == length && d_variables.cmpAssignmentUpperBound(basic) != 0);
}

bool LinearEqualityModule::nonbasicsAtUpperBounds(ArithVar basic) const {
  Assert(basicIsTracked(basic));
  RowIndex ridx = d_tableau.basicToRowIndex(basic);
  BoundCounts bcs = d_btracking[ridx].atBounds();
  uint32_t length = d_tableau.basicRowLength(basic);
  uint32_t ubc = bcs.upperBoundCount();
  // See the comment for nonbasicsAtLowerBounds()

  return (ubc == length) ||
    (ubc + 1 == length && d_variables.cmpAssignmentLowerBound(basic) != 0);
}

void LinearEqualityModule::trackingMultiplyRow(RowIndex ridx, int sgn) {
  Assert(rowIndexIsTracked(ridx));
  Assert(sgn != 0);
  if(sgn < 0){
    BoundsInfo& bi = d_btracking.get(ridx);
    bi = bi.multiplyBySgn(sgn);
  }
}

void LinearEqualityModule::trackingCoefficientChange(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn){
  Assert(oldSgn != currSgn);
  BoundsInfo nb_inf = d_variables.boundsInfo(nb);

  Assert(rowIndexIsTracked(ridx));

  BoundsInfo& row_bi = d_btracking.get(ridx);
  row_bi.addInSgn(nb_inf, oldSgn, currSgn);
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

  ConstraintP bound = ub ?
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
    if (d_upperBoundDifference.nothing()
        || nbDiff <= d_upperBoundDifference.value())
    {
      return false;
    }
  }else{
    if (d_lowerBoundDifference.nothing()
        || nbDiff >= d_lowerBoundDifference.value())
    {
      return false;
    }
  }

  // Assume past this point, nb will be in error if this pivot is done
  ArithVar nb = entry.getColVar();
  RowIndex ridx = entry.getRowIndex();
  ArithVar basic = d_tableau.rowIndexToBasic(ridx);
  Assert(rowIndexIsTracked(ridx));
  int coeffSgn = entry.getCoefficient().sgn();


  // if bToUB, then basic is going to be set to its upperbound
  // if not bToUB, then basic is going to be set to its lowerbound

  // Different steps of solving for this:
  // 1) y = a * x + \sum b * z
  // 2) -a * x = -y + \sum b * z
  // 3) x = (-1/a) * ( -y + \sum b * z)

  BoundCounts bc = d_btracking[ridx].atBounds();

  // 1) y = a * x + \sum b * z
  // Get bc(\sum b * z)
  BoundCounts sumOnly = bc - d_variables.atBoundCounts(nb).multiplyBySgn(coeffSgn);

  // y's bounds in the proposed model
  int yWillBeAtUb = (bToUB || d_variables.boundsAreEqual(basic)) ? 1 : 0;
  int yWillBeAtLb = (!bToUB || d_variables.boundsAreEqual(basic)) ? 1 : 0;
  BoundCounts ysBounds(yWillBeAtLb, yWillBeAtUb);

  // 2) -a * x = -y + \sum b * z
  // Get bc(-y + \sum b * z)
  sumOnly.addInChange(-1, d_variables.atBoundCounts(basic), ysBounds);

  // 3) x = (-1/a) * ( -y + \sum b * z)
  // Get bc((-1/a) * ( -y + \sum b * z))
  BoundCounts xsBoundsAfterPivot = sumOnly.multiplyBySgn(-coeffSgn);

  uint32_t length = d_tableau.basicRowLength(basic);
  if(nbSgn > 0){
    // Only check for the upper bound being violated
    return xsBoundsAfterPivot.lowerBoundCount() + 1 == length;
  }else{
    // Only check for the lower bound being violated
    return xsBoundsAfterPivot.upperBoundCount() + 1 == length;
  }
}

UpdateInfo LinearEqualityModule::mkConflictUpdate(const Tableau::Entry& entry, bool ub) const{
  ArithVar currBasic = d_tableau.rowIndexToBasic(entry.getRowIndex());
  ArithVar nb = entry.getColVar();

  ConstraintP bound = ub ?
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
    ConstraintP ub = d_variables.getUpperBoundConstraint(nb);
    d_upperBoundDifference = ub->getValue() - d_variables.getAssignment(nb);
    Border border(ub, d_upperBoundDifference.value(), false, NULL, true);
    Debug("handleBorders") << "push back increasing " << border << endl;
    d_increasing.push_back(border);
  }
  if(d_variables.hasLowerBound(nb)){
    ConstraintP lb = d_variables.getLowerBoundConstraint(nb);
    d_lowerBoundDifference = lb->getValue() - d_variables.getAssignment(nb);
    Border border(lb, d_lowerBoundDifference.value(), false, NULL, false);
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
      Assert((heap.direction() > 0) ? (blockValue < top.d_diff)
                                    : (blockValue > top.d_diff));
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
