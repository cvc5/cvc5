
#include "theory/arith/partial_model.h"
#include "util/output.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::theory::arith::partial_model;

void ArithPartialModel::setUpperBound(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  d_UpperBoundMap[x] = r;
}

void ArithPartialModel::setLowerBound(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  d_LowerBoundMap[x] = r;
}

void ArithPartialModel::setAssignment(TNode x, const DeltaRational& r){
  Assert(x.getMetaKind() == CVC4::kind::metakind::VARIABLE);

  if(d_savingAssignments){
    d_history.push_back(make_pair(x,r));
  }

  DeltaRational* c;
  if(x.getAttribute(partial_model::Assignment(), c)){
    *c = r;
    Debug("partial_model") << "pm: updating the assignment to" << x
                           << " now " << r <<endl;
  }else{
    Debug("partial_model") << "pm: constructing an assignment for " << x
                           << " initially " << r <<endl;

    c = new DeltaRational(r);
    x.setAttribute(partial_model::Assignment(), c);
  }
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

  d_savingAssignments = false;

  if(revert){
    while(!d_history.empty()){
      pair<TNode, DeltaRational>& curr = d_history.back();
      d_history.pop_back();

      TNode x = curr.first;

      DeltaRational* c;
      bool hasAssignment = x.getAttribute(partial_model::Assignment(), c);
      Assert(hasAssignment);

      *c = curr.second;
    }
  }else{
    d_history.clear();
  }

}
