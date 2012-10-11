/*********************                                                        */
/*! \file linear_equality.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This implements the LinearEqualityModule.
 **
 ** This implements the LinearEqualityModule.
 **/


#include "theory/arith/linear_equality.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

/* Explicitly instatiate this function. */
template void LinearEqualityModule::propagateNonbasics<true>(ArithVar basic, Constraint c);
template void LinearEqualityModule::propagateNonbasics<false>(ArithVar basic, Constraint c);

LinearEqualityModule::Statistics::Statistics():
  d_statPivots("theory::arith::pivots",0),
  d_statUpdates("theory::arith::updates",0),
  d_pivotTime("theory::arith::pivotTime")
{
  StatisticsRegistry::registerStat(&d_statPivots);
  StatisticsRegistry::registerStat(&d_statUpdates);

  StatisticsRegistry::registerStat(&d_pivotTime);
}

LinearEqualityModule::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_statPivots);
  StatisticsRegistry::unregisterStat(&d_statUpdates);
  StatisticsRegistry::unregisterStat(&d_pivotTime);
}

void LinearEqualityModule::update(ArithVar x_i, const DeltaRational& v){
  Assert(!d_tableau.isBasic(x_i));
  DeltaRational assignment_x_i = d_partialModel.getAssignment(x_i);
  ++(d_statistics.d_statUpdates);

  Debug("arith") <<"update " << x_i << ": "
                 << assignment_x_i << "|-> " << v << endl;
  DeltaRational diff = v - assignment_x_i;

  //Assert(matchingSets(d_tableau, x_i));
  Tableau::ColIterator basicIter = d_tableau.colIterator(x_i);
  for(; !basicIter.atEnd(); ++basicIter){
    const Tableau::Entry& entry = *basicIter;
    Assert(entry.getColVar() == x_i);

    ArithVar x_j = d_tableau.rowIndexToBasic(entry.getRowIndex());
    //ReducedRowVector& row_j = d_tableau.lookup(x_j);

    //const Rational& a_ji = row_j.lookup(x_i);
    const Rational& a_ji = entry.getCoefficient();

    const DeltaRational& assignment = d_partialModel.getAssignment(x_j);
    DeltaRational  nAssignment = assignment+(diff * a_ji);
    d_partialModel.setAssignment(x_j, nAssignment);

    d_basicVariableUpdates(x_j);
  }

  d_partialModel.setAssignment(x_i, v);

  //double difference = ((double)d_tableau.getNumRows()) - ((double) d_tableau.getRowLength(x_i));

  //(d_statistics.d_avgNumRowsNotContainingOnUpdate).addEntry(difference);
  if(Debug.isOn("paranoid:check_tableau")){  debugCheckTableau(); }
}

void LinearEqualityModule::pivotAndUpdate(ArithVar x_i, ArithVar x_j, DeltaRational& v){
  Assert(x_i != x_j);

  TimerStat::CodeTimer codeTimer(d_statistics.d_pivotTime);

  if(Debug.isOn("arith::simplex:row")){ debugPivot(x_i, x_j); }

  RowIndex ridx = d_tableau.basicToRowIndex(x_i);
  const Tableau::Entry& entry_ij =  d_tableau.findEntry(ridx, x_j);
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
    const Tableau::Entry& entry = *iter;
    Assert(entry.getColVar() == x_j);
    RowIndex currRow = entry.getRowIndex();
    if(ridx != currRow ){
      ArithVar x_k = d_tableau.rowIndexToBasic(currRow);
      const Rational& a_kj = entry.getCoefficient();
      DeltaRational nextAssignment = d_partialModel.getAssignment(x_k) + (theta * a_kj);
      d_partialModel.setAssignment(x_k, nextAssignment);

      d_basicVariableUpdates(x_k);
    }
  }

  // Pivots
  ++(d_statistics.d_statPivots);

  d_tableau.pivot(x_i, x_j);

  d_basicVariableUpdates(x_j);

  if(Debug.isOn("matrix")){
    d_tableau.printMatrix();
  }
}


void LinearEqualityModule::debugPivot(ArithVar x_i, ArithVar x_j){
  Debug("arith::pivot") << "debugPivot("<< x_i  <<"|->"<< x_j << ")" << endl;

  for(Tableau::RowIterator iter = d_tableau.basicRowIterator(x_i); !iter.atEnd(); ++iter){
    const Tableau::Entry& entry = *iter;

    ArithVar var = entry.getColVar();
    const Rational& coeff = entry.getCoefficient();
    DeltaRational beta = d_partialModel.getAssignment(var);
    Debug("arith::pivot") << var << beta << coeff;
    if(d_partialModel.hasLowerBound(var)){
      Debug("arith::pivot") << "(lb " << d_partialModel.getLowerBound(var) << ")";
    }
    if(d_partialModel.hasUpperBound(var)){
      Debug("arith::pivot") << "(up " << d_partialModel.getUpperBound(var) << ")";
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
      d_partialModel.getUpperBound(nonbasic):
      d_partialModel.getLowerBound(nonbasic);

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

    const DeltaRational& assignment = d_partialModel.getAssignment(nonbasic, useSafe);
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

template <bool upperBound>
void LinearEqualityModule::propagateNonbasics(ArithVar basic, Constraint c){
  Assert(d_tableau.isBasic(basic));
  Assert(c->getVariable() == basic);
  Assert(!c->assertedToTheTheory());
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
        bound = d_partialModel.getLowerBoundConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_partialModel.getUpperBoundConstraint(nonbasic);
      }
    }else{
      if(sgn < 0){
        bound = d_partialModel.getUpperBoundConstraint(nonbasic);
      }else{
        Assert(sgn > 0);
        bound = d_partialModel.getLowerBoundConstraint(nonbasic);
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

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
