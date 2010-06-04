/*********************                                                        */
/*! \file partial_model.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
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

void ArithPartialModel::setUpperBound(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setUpperBound(" << x << "," << r << ")" << endl;

  d_UpperBoundMap[x] = r;
}

void ArithPartialModel::setLowerBound(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  Debug("partial_model") << "setLowerBound(" << x << "," << r << ")" << endl;
  d_LowerBoundMap[x] = r;
}

void ArithPartialModel::setAssignment(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  if(d_savingAssignments){
    DeltaRational current = getAssignment(x);
    d_history.push_back(make_pair(x,current));
  }

  Assert(x.hasAttribute(partial_model::Assignment()));

  DeltaRational* c = x.getAttribute(partial_model::Assignment());
  *c = r;
  Debug("partial_model") << "pm: updating the assignment to" << x
                         << " now " << r <<endl;
}

void ArithPartialModel::initialize(TNode x, const DeltaRational& r){
   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);


   Assert(!x.hasAttribute(partial_model::Assignment()));
   DeltaRational* c = new DeltaRational(r);
   x.setAttribute(partial_model::Assignment(), c);

   Debug("partial_model") << "pm: constructing an assignment for " << x
                          << " initially " << (*c) <<endl;
}

/** Must know that the bound exists both calling this! */
DeltaRational ArithPartialModel::getUpperBound(TNode x) const {
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
  Assert(i != d_UpperBoundMap.end());

  return DeltaRational((*i).second);
}

DeltaRational ArithPartialModel::getLowerBound(TNode x) const{
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  Assert(i != d_LowerBoundMap.end());

  return DeltaRational((*i).second);
}


DeltaRational ArithPartialModel::getAssignment(TNode x) const{
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));
  return *assign;
}

DeltaRational ArithPartialModel::getSavedAssignment(TNode x) const{
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);
  if(d_savingAssignments){
    for(HistoryStack::const_iterator i = d_history.begin(); i != d_history.end(); ++i){
      pair<TNode, DeltaRational> curr = *i;
      if(curr.first == x){
        return DeltaRational(curr.second);
      }
    }
  }
  return getAssignment(x);
}


void ArithPartialModel::setLowerConstraint(TNode x, TNode constraint){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setLowerConstraint("
                         << x << ":" << constraint << ")" << endl;

  x.setAttribute(partial_model::LowerConstraint(),constraint);
}

void ArithPartialModel::setUpperConstraint(TNode x, TNode constraint){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  Debug("partial_model") << "setUpperConstraint("
                         << x << ":" << constraint << ")" << endl;

  x.setAttribute(partial_model::UpperConstraint(),constraint);
}

TNode ArithPartialModel::getLowerConstraint(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  TNode ret;
  AlwaysAssert(x.getAttribute(partial_model::LowerConstraint(),ret));
  return ret;
}

TNode ArithPartialModel::getUpperConstraint(TNode x){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  TNode ret;
  AlwaysAssert(x.getAttribute(partial_model::UpperConstraint(),ret));
  return ret;
}

// TNode CVC4::theory::arith::getLowerConstraint(TNode x){
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//   TNode ret;
//   AlwaysAssert(x.getAttribute(partial_model::LowerConstraint(),ret));
//   return ret;
// }

// TNode CVC4::theory::arith::getUpperConstraint(TNode x){
//   Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

//   TNode ret;
//   AlwaysAssert(x.getAttribute(partial_model::UpperConstraint(),ret));
//   return ret;
// }


bool ArithPartialModel::belowLowerBound(TNode x, DeltaRational& c, bool strict){
  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  if(i == d_LowerBoundMap.end()){
    // l = -\intfy
    // ? c < -\infty |-  _|_
    return false;
  }

  DeltaRational l = (*i).second;

  if(strict){
    return c < l;
  }else{
    return c <= l;
  }
}

bool ArithPartialModel::aboveUpperBound(TNode x, DeltaRational& c, bool strict){
  CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
  if(i == d_UpperBoundMap.end()){
    // u = -\intfy
    // ? u < -\infty |-  _|_
    return false;
  }
  DeltaRational u = (*i).second;

  if(strict){
    return c > u;
  }else{
    return c >= u;
  }
}

bool ArithPartialModel::strictlyBelowUpperBound(TNode x){
  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));

  CDDRationalMap::iterator i = d_UpperBoundMap.find(x);
  if(i == d_UpperBoundMap.end()){// u = \infty
    return true;
  }
  DeltaRational u = (*i).second;

  return *assign < u;
}

bool ArithPartialModel::strictlyAboveLowerBound(TNode x){
  DeltaRational* assign;
  AlwaysAssert(x.getAttribute(partial_model::Assignment(),assign));

  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  if(i == d_LowerBoundMap.end()){// l = \infty
    return true;
  }
  DeltaRational l = (*i).second;
  return l < *assign;
}

bool ArithPartialModel::assignmentIsConsistent(TNode x){
  DeltaRational beta = getAssignment(x);

  bool above_li = !belowLowerBound(x,beta,true);
  bool below_ui = !aboveUpperBound(x,beta,true);

  //l_i <= beta(x_i) <= u_i
  return  above_li && below_ui;
}

void ArithPartialModel::beginRecordingAssignments(){
  Assert(!d_savingAssignments);
  Assert(d_history.empty());

  d_savingAssignments = true;
}


void ArithPartialModel::stopRecordingAssignments(bool revert){
  Assert(d_savingAssignments);

  d_savingAssignments = false; //

  if(revert){
    while(!d_history.empty()){
      pair<TNode, DeltaRational>& curr = d_history.back();

      setAssignment(curr.first,curr.second);

      d_history.pop_back();
    }
  }else{
    d_history.clear();
  }

}
void ArithPartialModel::printModel(TNode x){

  Debug("model") << "model" << x << ":"<< getAssignment(x) << " ";

  CDDRationalMap::iterator i = d_LowerBoundMap.find(x);
  if(i != d_LowerBoundMap.end()){
    DeltaRational l = (*i).second;
    Debug("model") << l << " ";
    Debug("model") << getLowerConstraint(x) << " ";
  }else{
    Debug("model") << "no lb ";
  }

  i = d_UpperBoundMap.find(x);
  if(i != d_UpperBoundMap.end()){
    DeltaRational u = (*i).second;
    Debug("model") << u << " ";
    Debug("model") << getUpperConstraint(x) << " ";
  }else{
    Debug("model") << "no ub ";
  }
  Debug("model") << endl;
}
