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
using namespace CVC4::theory::arith::partial_model;

void ArithPartialModel::setUpperBound(ArithVar x, const DeltaRational& r){
  //Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setUpperBound(" << x << "," << r << ")" << endl;
  //x.setAttribute(partial_model::HasHadABound(), true);
  d_hasHadABound[x] = true;

  d_upperBound.set(x,r);
}

void ArithPartialModel::setLowerBound(ArithVar x, const DeltaRational& r){
  //Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  // Debug("partial_model") << "setLowerBound(" << x << "," << r << ")" << endl;
//   x.setAttribute(partial_model::HasHadABound(), true);

//   d_LowerBoundMap[x] = r;
  d_hasHadABound[x] = true;
  d_lowerBound.set(x,r);
}

void ArithPartialModel::setAssignment(ArithVar x, const DeltaRational& r){
  //Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  //Assert(x.hasAttribute(partial_model::Assignment()));
  //Assert(x.hasAttribute(partial_model::SafeAssignment()));

//   DeltaRational* curr = x.getAttribute(partial_model::Assignment());

//   DeltaRational* saved = x.getAttribute(partial_model::SafeAssignment());
//   if(saved == NULL){
//     saved = new DeltaRational(*curr);
//     x.setAttribute(partial_model::SafeAssignment(), saved);
//     d_history.push_back(x);
//   }

//   *curr = r;
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
  // Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
//   Assert(x.hasAttribute(partial_model::Assignment()));
//   Assert(x.hasAttribute(partial_model::SafeAssignment()));

//   DeltaRational* curr = x.getAttribute(partial_model::Assignment());
//   DeltaRational* saved = x.getAttribute(partial_model::SafeAssignment());



//   if(safe == r){
//     if(saved != NULL){
//       x.setAttribute(partial_model::SafeAssignment(), NULL);
//       delete saved;
//     }
//   }else{
//     if(saved == NULL){
//       saved = new DeltaRational(safe);
//       x.setAttribute(partial_model::SafeAssignment(), saved);
//     }else{
//       *saved = safe;
//     }
//     d_history.push_back(x);
//   }
//   *curr = r;

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
//    Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//    Assert(!x.hasAttribute(partial_model::Assignment()));
//    Assert(!x.hasAttribute(partial_model::SafeAssignment()));

//    DeltaRational* c = new DeltaRational(r);
//    x.setAttribute(partial_model::Assignment(), c);
//    x.setAttribute(partial_model::SafeAssignment(), NULL);

//    Debug("partial_model") << "pm: constructing an assignment for " << x
//                           << " initially " << (*c) <<endl;

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

//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//   CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
//   Assert(i != d_UpperBoundMap.end());

//   return DeltaRational((*i).second);
}

const DeltaRational& ArithPartialModel::getLowerBound(ArithVar x) {
  Assert(inMaps(x));
  Assert(!d_lowerConstraint[x].isNull());

  return d_lowerBound[x];

//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//   CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
//   Assert(i != d_LowerBoundMap.end());

//   return DeltaRational((*i).second);
}

const DeltaRational& ArithPartialModel::getSafeAssignment(ArithVar x) const{
  Assert(inMaps(x));
  if(d_hasSafeAssignment[x]){
    return d_safeAssignment[x];
  }else{
    return d_assignment[x];
  }
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
//   Assert( x.hasAttribute(SafeAssignment()));

//   DeltaRational* safeAssignment = x.getAttribute(SafeAssignment());
//   if(safeAssignment != NULL){
//     return *safeAssignment;
//   }else{
//     return getAssignment(x); //The current assignment is safe.
//   }
}

const DeltaRational& ArithPartialModel::getAssignment(ArithVar x) const{
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//   DeltaRational* assign;
//   AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));
//   return *assign;
  Assert(inMaps(x));
  return d_assignment[x];
}



void ArithPartialModel::setLowerConstraint(ArithVar x, TNode constraint){
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setLowerConstraint("
                         << x << ":" << constraint << ")" << endl;

//   x.setAttribute(partial_model::LowerConstraint(),constraint);

  Assert(inMaps(x));
  d_lowerConstraint.set(x,constraint);

}

void ArithPartialModel::setUpperConstraint(ArithVar x, TNode constraint){
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setUpperConstraint("
                         << x << ":" << constraint << ")" << endl;

//   x.setAttribute(partial_model::UpperConstraint(),constraint);
  Assert(inMaps(x));
  d_upperConstraint.set(x, constraint);
}

TNode ArithPartialModel::getLowerConstraint(ArithVar x){
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//   TNode ret;
//   AlwaysAssert(x.getAttribute(partial_model::LowerConstraint(),ret));
//   return ret;

  Assert(inMaps(x));
  Assert(!d_lowerConstraint[x].isNull());
  return d_lowerConstraint[x];
}

TNode ArithPartialModel::getUpperConstraint(ArithVar x){
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//   TNode ret;
//   AlwaysAssert(x.getAttribute(partial_model::UpperConstraint(),ret));
//   return ret;
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
//   CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
//   if(i == d_LowerBoundMap.end()){
//     // l = -\intfy
//     // ? c < -\infty |-  _|_
//     return false;
//   }

//   const DeltaRational& l = (*i).second;

//   if(strict){
//     return c < l;
//   }else{
//     return c <= l;
//   }
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
//   CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
//   if(i == d_UpperBoundMap.end()){
//     // u = -\intfy
//     // ? u < -\infty |-  _|_
//     return false;
//   }
//   const DeltaRational& u = (*i).second;

//   if(strict){
//     return c > u;
//   }else{
//     return c >= u;
//   }
}

bool ArithPartialModel::hasBounds(ArithVar x){
  return
    !d_lowerConstraint[x].isNull() || !d_upperConstraint[x].isNull();
  // return
//     d_UpperBoundMap.find(x) != d_UpperBoundMap.end() ||
//     d_LowerBoundMap.find(x) != d_LowerBoundMap.end();
}

bool ArithPartialModel::strictlyBelowUpperBound(ArithVar x){
  Assert(inMaps(x));
  if(d_upperConstraint[x].isNull()){ // u = \infty
    return true;
  }
  return d_assignment[x] < d_upperBound[x];
//   DeltaRational* assign;
//   AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));

//   CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
//   if(i == d_UpperBoundMap.end()){// u = \infty
//     return true;
//   }

//   const DeltaRational& u = (*i).second;
//   return (*assign) < u;
}

bool ArithPartialModel::strictlyAboveLowerBound(ArithVar x){
  Assert(inMaps(x));
  if(d_lowerConstraint[x].isNull()){ // l = -\infty
    return true;
  }
  return  d_lowerBound[x] < d_assignment[x];

//   DeltaRational* assign;
//   AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));

//   CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
//   if(i == d_LowerBoundMap.end()){// l = \infty
//     return true;
//   }

//   const DeltaRational& l = (*i).second;
//   return l < *assign;
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
//     Assert(x.hasAttribute(SafeAssignment()));
//     Assert(x.hasAttribute(Assignment()));

//     DeltaRational* safeAssignment = x.getAttribute(SafeAssignment());

//     if(revert){
//       DeltaRational* assign = x.getAttribute(Assignment());
//       *assign = *safeAssignment;
//     }
//     x.setAttribute(partial_model::SafeAssignment(), NULL);
//     delete safeAssignment;
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
//   Debug("model") << "model" << x << ":"<< getAssignment(x) << " ";

//   CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
//   if(i != d_LowerBoundMap.end()){
//     DeltaRational l = (*i).second;
//     Debug("model") << l << " ";
//     Debug("model") << getLowerConstraint(x) << " ";
//   }else{
//     Debug("model") << "no lb ";
//   }

//   i = d_UpperBoundMap.find(x);
//   if(i != d_UpperBoundMap.end()){
//     DeltaRational u = (*i).second;
//     Debug("model") << u << " ";
//     Debug("model") << getUpperConstraint(x) << " ";
//   }else{
//     Debug("model") << "no ub ";
//   }
//   Debug("model") << endl;
}
