/*********************                                                        */
/*! \file partial_model.cpp
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


#include "theory/arith/partial_model.h"
#include "util/output.h"
#include "theory/arith/constraint.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

ArithPartialModel::ArithPartialModel(context::Context* c)
 : d_mapSize(0),
   d_hasSafeAssignment(),
   d_assignment(),
   d_safeAssignment(),
   d_ubc(c),
   d_lbc(c),
   d_deltaIsSafe(false),
   d_delta(-1,1),
   d_history()
{ }

bool ArithPartialModel::boundsAreEqual(ArithVar x) const{
  if(hasLowerBound(x) && hasUpperBound(x)){
    return getUpperBound(x) == getLowerBound(x);
  }else{
    return false;
  }
}

void ArithPartialModel::setAssignment(ArithVar x, const DeltaRational& r){
   Debug("partial_model") << "pm: updating the assignment to" << x
                          << " now " << r <<endl;
  if(!d_hasSafeAssignment[x]){
    d_safeAssignment[x] = d_assignment[x];
    d_hasSafeAssignment[x] = true;
    d_history.push_back(x);
  }

  d_deltaIsSafe = false;
  d_assignment[x] = r;
}
void ArithPartialModel::setAssignment(ArithVar x, const DeltaRational& safe, const DeltaRational& r){
   Debug("partial_model") << "pm: updating the assignment to" << x
                          << " now " << r <<endl;
  if(safe == r){
    d_hasSafeAssignment[x] = false;
  }else{
    d_safeAssignment[x] = safe;

    if(!d_hasSafeAssignment[x]){
      d_hasSafeAssignment[x] = true;
      d_history.push_back(x);
    }
  }

  d_deltaIsSafe = false;
  d_assignment[x] = r;
}

bool ArithPartialModel::equalSizes(){
  return
    d_mapSize == d_hasSafeAssignment.size() &&
    d_mapSize == d_assignment.size() &&
    d_mapSize == d_safeAssignment.size() &&
    d_mapSize == d_ubc.size() &&
    d_mapSize == d_lbc.size();
}

void ArithPartialModel::initialize(ArithVar x, const DeltaRational& r){
  Assert(x == d_mapSize);
  Assert(equalSizes());
  ++d_mapSize;

  d_hasSafeAssignment.push_back( false );
  // Is wirth mentioning that this is not strictly necessary, but this maintains the internal invariant
  // that when d_assignment is set this gets set.
  d_deltaIsSafe = false;
  d_assignment.push_back( r );
  d_safeAssignment.push_back( DeltaRational(0) );

  d_ubc.push_back(NullConstraint);
  d_lbc.push_back(NullConstraint);
}

/** Must know that the bound exists both calling this! */
const DeltaRational& ArithPartialModel::getUpperBound(ArithVar x) const {
  Assert(inMaps(x));
  Assert(hasUpperBound(x));

  return getUpperBoundConstraint(x)->getValue();
}

const DeltaRational& ArithPartialModel::getLowerBound(ArithVar x) const {
  Assert(inMaps(x));
  Assert(hasLowerBound(x));

  return getLowerBoundConstraint(x)->getValue();
}

const DeltaRational& ArithPartialModel::getSafeAssignment(ArithVar x) const{
  Assert(inMaps(x));
  if(d_hasSafeAssignment[x]){
    return d_safeAssignment[x];
  }else{
    return d_assignment[x];
  }
}

const DeltaRational& ArithPartialModel::getAssignment(ArithVar x, bool safe) const{
  Assert(inMaps(x));
  if(safe && d_hasSafeAssignment[x]){
    return d_safeAssignment[x];
  }else{
    return d_assignment[x];
  }
}

const DeltaRational& ArithPartialModel::getAssignment(ArithVar x) const{
  Assert(inMaps(x));
  return d_assignment[x];
}


void ArithPartialModel::setLowerBoundConstraint(Constraint c){
  AssertArgument(c != NullConstraint, "Cannot set a lower bound to NullConstraint.");
  AssertArgument(c->isEquality() || c->isLowerBound(),
                 "Constraint type must be set to an equality or UpperBound.");
  ArithVar x = c->getVariable();
  Debug("partial_model") << "setLowerBoundConstraint(" << x << ":" << c << ")" << endl;
  Assert(inMaps(x));
  Assert(greaterThanLowerBound(x, c->getValue()));

  d_deltaIsSafe = false;
  d_lbc.set(x, c);
}

void ArithPartialModel::setUpperBoundConstraint(Constraint c){
  AssertArgument(c != NullConstraint, "Cannot set a upper bound to NullConstraint.");
  AssertArgument(c->isEquality() || c->isUpperBound(),
                 "Constraint type must be set to an equality or UpperBound.");

  ArithVar x = c->getVariable();
  Debug("partial_model") << "setUpperBoundConstraint(" << x << ":" << c << ")" << endl;
  Assert(inMaps(x));
  Assert(lessThanUpperBound(x, c->getValue()));

  d_deltaIsSafe = false;
  d_ubc.set(x, c);
}

int ArithPartialModel::cmpToLowerBound(ArithVar x, const DeltaRational& c) const{
  if(!hasLowerBound(x)){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return 1;
  }else{
    return c.cmp(getLowerBound(x));
  }
}

int ArithPartialModel::cmpToUpperBound(ArithVar x, const DeltaRational& c) const{
  if(!hasUpperBound(x)){
    //u = \intfy
    // ? c > \infty |-  _|_
    return -1;
  }else{
    return c.cmp(getUpperBound(x));
  }
}

bool ArithPartialModel::equalsLowerBound(ArithVar x, const DeltaRational& c){
  if(!hasLowerBound(x)){
    return false;
  }else{
    return c == getLowerBound(x);
  }
}
bool ArithPartialModel::equalsUpperBound(ArithVar x, const DeltaRational& c){
  if(!hasUpperBound(x)){
    return false;
  }else{
    return c == getUpperBound(x);
  }
}

bool ArithPartialModel::hasEitherBound(ArithVar x) const{
  return hasLowerBound(x) || hasUpperBound(x);
}

bool ArithPartialModel::strictlyBelowUpperBound(ArithVar x) const{
  Assert(inMaps(x));
  if(!hasUpperBound(x)){ // u = \infty
    return true;
  }else{
    return d_assignment[x] < getUpperBound(x);
  }
}

bool ArithPartialModel::strictlyAboveLowerBound(ArithVar x) const{
  Assert(inMaps(x));
  if(!hasLowerBound(x)){ // l = -\infty
    return true;
  }else{
    return getLowerBound(x) < d_assignment[x];
  }
}

bool ArithPartialModel::assignmentIsConsistent(ArithVar x) const{
  const DeltaRational& beta = getAssignment(x);

  //l_i <= beta(x_i) <= u_i
  return  greaterThanLowerBound(x,beta) && lessThanUpperBound(x,beta);
}


void ArithPartialModel::clearSafeAssignments(bool revert){

  for(HistoryList::iterator i = d_history.begin(); i != d_history.end(); ++i){
    ArithVar x = *i;
    Assert(d_hasSafeAssignment[x]);
    d_hasSafeAssignment[x] = false;

    if(revert){
      d_assignment[x] = d_safeAssignment[x];
    }
  }

  if(revert && !d_history.empty()){
    d_deltaIsSafe = false;
  }

  d_history.clear();
}

void ArithPartialModel::revertAssignmentChanges(){
  clearSafeAssignments(true);
}
void ArithPartialModel::commitAssignmentChanges(){
  clearSafeAssignments(false);
}

void ArithPartialModel::printModel(ArithVar x){
  Debug("model") << "model" << x << ":"<< getAssignment(x) << " ";
  if(!hasLowerBound(x)){
    Debug("model") << "no lb ";
  }else{
    Debug("model") << getLowerBound(x) << " ";
    Debug("model") << getLowerBoundConstraint(x) << " ";
  }
  if(!hasUpperBound(x)){
    Debug("model") << "no ub ";
  }else{
    Debug("model") << getUpperBound(x) << " ";
    Debug("model") << getUpperBoundConstraint(x) << " ";
  }
  Debug("model") << endl;
}

void ArithPartialModel::deltaIsSmallerThan(const DeltaRational& l, const DeltaRational& u){
  const Rational& c = l.getNoninfinitesimalPart();
  const Rational& k = l.getInfinitesimalPart();
  const Rational& d = u.getNoninfinitesimalPart();
  const Rational& h = u.getInfinitesimalPart();

  if(c < d && k > h){
    Rational ep = (d-c)/(k-h);
    if(ep < d_delta){
      d_delta = ep;
    }
  }
}

void ArithPartialModel::computeDelta(const Rational& init){
  Assert(!d_deltaIsSafe);
  d_delta = init;

  for(ArithVar x = 0; x < d_mapSize; ++x){
    const DeltaRational& a = getAssignment(x);
    if(hasLowerBound(x)){
      const DeltaRational& l = getLowerBound(x);
      deltaIsSmallerThan(l,a);
    }
    if(hasUpperBound(x)){
      const DeltaRational& u = getUpperBound(x);
      deltaIsSmallerThan(a,u);
    }
  }
  d_deltaIsSafe = true;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
