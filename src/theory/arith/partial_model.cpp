/*********************                                                        */
/*! \file partial_model.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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


#include "theory/arith/partial_model.h"
#include "util/output.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

void ArithPartialModel::setUpperBound(ArithVar x, const DeltaRational& r){
  d_deltaIsSafe = false;

  Debug("partial_model") << "setUpperBound(" << x << "," << r << ")" << endl;
  d_hasHadABound[x] = true;
  d_upperBound.set(x,r);
}

void ArithPartialModel::setLowerBound(ArithVar x, const DeltaRational& r){
  d_deltaIsSafe = false;

  d_hasHadABound[x] = true;
  d_lowerBound.set(x,r);
}

void ArithPartialModel::setAssignment(ArithVar x, const DeltaRational& r){
   Debug("partial_model") << "pm: updating the assignment to" << x
                          << " now " << r <<endl;
  if(!d_hasSafeAssignment[x]){
    d_safeAssignment[x] = d_assignment[x];
    d_hasSafeAssignment[x] = true;
    d_history.push_back(x);
  }
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
  d_assignment[x] = r;
}

bool ArithPartialModel::equalSizes(){
  return d_mapSize == d_hasHadABound.size() &&
    d_mapSize == d_hasSafeAssignment.size() &&
    d_mapSize == d_assignment.size() &&
    d_mapSize == d_safeAssignment.size() &&
    d_mapSize == d_upperBound.size() &&
    d_mapSize == d_lowerBound.size() &&
    d_mapSize == d_upperConstraint.size() &&
    d_mapSize == d_lowerConstraint.size();
}

void ArithPartialModel::initialize(ArithVar x, const DeltaRational& r){
  Assert(x == d_mapSize);
  Assert(equalSizes());
  ++d_mapSize;


  d_hasHadABound.push_back( false );

  d_hasSafeAssignment.push_back( false );
  d_assignment.push_back( r );
  d_safeAssignment.push_back( DeltaRational(0) );

  d_upperBound.push_back( DeltaRational(0) );
  d_lowerBound.push_back( DeltaRational(0) );

  d_upperConstraint.push_back( TNode::null() );
  d_lowerConstraint.push_back( TNode::null() );
}

/** Must know that the bound exists both calling this! */
const DeltaRational& ArithPartialModel::getUpperBound(ArithVar x) {
  Assert(inMaps(x));
  Assert(!d_upperConstraint[x].isNull());

  return d_upperBound[x];
}

const DeltaRational& ArithPartialModel::getLowerBound(ArithVar x) {
  Assert(inMaps(x));
  Assert(!d_lowerConstraint[x].isNull());

  return d_lowerBound[x];
}

const DeltaRational& ArithPartialModel::getSafeAssignment(ArithVar x) const{
  Assert(inMaps(x));
  if(d_hasSafeAssignment[x]){
    return d_safeAssignment[x];
  }else{
    return d_assignment[x];
  }
}

const DeltaRational& ArithPartialModel::getAssignment(ArithVar x) const{
  Assert(inMaps(x));
  return d_assignment[x];
}



void ArithPartialModel::setLowerConstraint(ArithVar x, TNode constraint){
  Debug("partial_model") << "setLowerConstraint("
                         << x << ":" << constraint << ")" << endl;
  Assert(inMaps(x));
  d_lowerConstraint.set(x,constraint);

}

void ArithPartialModel::setUpperConstraint(ArithVar x, TNode constraint){
  Debug("partial_model") << "setUpperConstraint("
                         << x << ":" << constraint << ")" << endl;
  Assert(inMaps(x));
  d_upperConstraint.set(x, constraint);
}

TNode ArithPartialModel::getLowerConstraint(ArithVar x){
  Assert(inMaps(x));
  Assert(!d_lowerConstraint[x].isNull());
  return d_lowerConstraint[x];
}

TNode ArithPartialModel::getUpperConstraint(ArithVar x){
  Assert(inMaps(x));
  Assert(!d_upperConstraint[x].isNull());
  return d_upperConstraint[x];
}



bool ArithPartialModel::belowLowerBound(ArithVar x, const DeltaRational& c, bool strict){
  if(d_lowerConstraint[x].isNull()){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return false;
  }
  if(strict){
    return c < d_lowerBound[x];
  }else{
    return c <= d_lowerBound[x];
  }
}

bool ArithPartialModel::aboveUpperBound(ArithVar x, const DeltaRational& c, bool strict){
  if(d_upperConstraint[x].isNull()){
    // u = \intfy
    // ? c > \infty |-  _|_
    return false;
  }
  if(strict){
    return c > d_upperBound[x];
  }else{
    return c >= d_upperBound[x];
  }
}

bool ArithPartialModel::hasBounds(ArithVar x){
  return !d_lowerConstraint[x].isNull() || !d_upperConstraint[x].isNull();
}

bool ArithPartialModel::strictlyBelowUpperBound(ArithVar x){
  Assert(inMaps(x));
  if(d_upperConstraint[x].isNull()){ // u = \infty
    return true;
  }
  return d_assignment[x] < d_upperBound[x];
}

bool ArithPartialModel::strictlyAboveLowerBound(ArithVar x){
  Assert(inMaps(x));
  if(d_lowerConstraint[x].isNull()){ // l = -\infty
    return true;
  }
  return  d_lowerBound[x] < d_assignment[x];
}

bool ArithPartialModel::assignmentIsConsistent(ArithVar x){
  const DeltaRational& beta = getAssignment(x);

  //l_i <= beta(x_i) <= u_i
  return  !belowLowerBound(x,beta,true) && !aboveUpperBound(x,beta,true);
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
  if(d_lowerConstraint[x].isNull()){
    Debug("model") << "no lb ";
  }else{
    Debug("model") << getLowerBound(x) << " ";
    Debug("model") << getLowerConstraint(x) << " ";
  }
  if(d_upperConstraint[x].isNull()){
    Debug("model") << "no ub ";
  }else{
    Debug("model") << getUpperBound(x) << " ";
    Debug("model") << getUpperConstraint(x) << " ";
  }
}

void ArithPartialModel::computeDelta(){
  Assert(!d_deltaIsSafe);
  d_deltaIsSafe = true;
  d_delta = 1;

  for(ArithVar x = 0; x < d_mapSize; ++x){
    if(hasBounds(x)){
      const DeltaRational& l = getLowerBound(x);
      const DeltaRational& u = getUpperBound(x);
      // c + k\ep <= d + h\ep
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
  }
}
