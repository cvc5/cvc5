/*********************                                                        */
/*! \file simplex_update.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This implements UpdateInfo.
 **
 ** This implements the UpdateInfo.
 **/


#include "theory/arith/simplex_update.h"
#include "theory/arith/constraint.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {


UpdateInfo::UpdateInfo():
  d_nonbasic(ARITHVAR_SENTINEL),
  d_nonbasicDirection(0),
  d_nonbasicDelta(),
  d_foundConflict(false),
  d_errorsChange(),
  d_focusDirection(),
  d_tableauCoefficient(),
  d_limiting(NullConstraint),
  d_witness(AntiProductive)
{}

UpdateInfo::UpdateInfo(ArithVar nb, int dir):
  d_nonbasic(nb),
  d_nonbasicDirection(dir),
  d_nonbasicDelta(),
  d_foundConflict(false),
  d_errorsChange(),
  d_focusDirection(),
  d_tableauCoefficient(),
  d_limiting(NullConstraint),
  d_witness(AntiProductive)
{
  Assert(dir == 1 || dir == -1);
}

UpdateInfo::UpdateInfo(bool conflict, ArithVar nb, const DeltaRational& delta, const Rational& r, ConstraintP c):
  d_nonbasic(nb),
  d_nonbasicDirection(delta.sgn()),
  d_nonbasicDelta(delta),
  d_foundConflict(true),
  d_errorsChange(),
  d_focusDirection(),
  d_tableauCoefficient(&r),
  d_limiting(c),
  d_witness(ConflictFound)
{
  Assert(conflict);
}

UpdateInfo UpdateInfo::conflict(ArithVar nb, const DeltaRational& delta, const Rational& r, ConstraintP lim){
  return UpdateInfo(true, nb, delta, r, lim);
}

void UpdateInfo::updateUnbounded(const DeltaRational& delta, int ec, int f){
  d_limiting = NullConstraint;
  d_nonbasicDelta = delta;
  d_errorsChange = ec;
  d_focusDirection = f;
  d_tableauCoefficient.clear();
  updateWitness();
  Assert(unbounded());
  Assert(improvement(d_witness));
  Assert(!describesPivot());
  Assert(debugSgnAgreement());
}
void UpdateInfo::updatePureFocus(const DeltaRational& delta, ConstraintP c){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange.clear();
  d_focusDirection = 1;
  d_tableauCoefficient.clear();
  updateWitness();
  Assert(!describesPivot());
  Assert(improvement(d_witness));
  Assert(debugSgnAgreement());
}

void UpdateInfo::updatePivot(const DeltaRational& delta, const Rational& r, ConstraintP c){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange.clear();
  d_focusDirection.clear();
  updateWitness();
  Assert(describesPivot());
  Assert(debugSgnAgreement());
}

void UpdateInfo::updatePivot(const DeltaRational& delta, const Rational& r, ConstraintP c, int ec){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange = ec;
  d_focusDirection.clear();
  d_tableauCoefficient = &r;
  updateWitness();
  Assert(describesPivot());
  Assert(debugSgnAgreement());
}

void UpdateInfo::witnessedUpdate(const DeltaRational& delta, ConstraintP c, int ec, int fd){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange = ec;
  d_focusDirection = fd;
  d_tableauCoefficient.clear();
  updateWitness();
  Assert(describesPivot() || improvement(d_witness));
  Assert(debugSgnAgreement());
}

void UpdateInfo::update(const DeltaRational& delta, const Rational& r, ConstraintP c, int ec, int fd){
  d_limiting = c;
  d_nonbasicDelta = delta;
  d_errorsChange = ec;
  d_focusDirection = fd;
  d_tableauCoefficient = &r;
  updateWitness();
  Assert(describesPivot() || improvement(d_witness));
  Assert(debugSgnAgreement());
}

bool UpdateInfo::describesPivot() const {
  return !unbounded() && d_nonbasic != d_limiting->getVariable();
}

void UpdateInfo::output(std::ostream& out) const{
  out << "{UpdateInfo"
      << ", nb = " << d_nonbasic
      << ", dir = " << d_nonbasicDirection
      << ", delta = " << d_nonbasicDelta
      << ", conflict = " << d_foundConflict
      << ", errorChange = " << d_errorsChange
      << ", focusDir = " << d_focusDirection
      << ", witness = " << d_witness
      << ", limiting = " << d_limiting
      << "}";
}

ArithVar UpdateInfo::leaving() const{
  Assert(describesPivot());

  return d_limiting->getVariable();
}

std::ostream& operator<<(std::ostream& out, const UpdateInfo& up){
  up.output(out);
  return out;
}


std::ostream& operator<<(std::ostream& out,  WitnessImprovement w){
  switch(w){
  case ConflictFound:
    out << "ConflictFound"; break;
  case ErrorDropped:
    out << "ErrorDropped"; break;
  case FocusImproved:
    out << "FocusImproved"; break;
  case FocusShrank:
    out << "FocusShrank"; break;
  case Degenerate:
    out << "Degenerate"; break;
  case BlandsDegenerate:
    out << "BlandsDegenerate"; break;
  case HeuristicDegenerate:
    out << "HeuristicDegenerate"; break;
  case AntiProductive:
    out << "AntiProductive"; break;
  }
  return out;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
