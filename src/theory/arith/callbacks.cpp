/*********************                                                        */
/*! \file callbacks.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/callbacks.h"
#include "theory/arith/theory_arith_private.h"

namespace CVC4 {
namespace theory {
namespace arith {

SetupLiteralCallBack::SetupLiteralCallBack(TheoryArithPrivate& ta)
  : d_arith(ta)
{}
void SetupLiteralCallBack::operator()(TNode lit){
  TNode atom = (lit.getKind() == kind::NOT) ? lit[0] : lit;
  if(!d_arith.isSetup(atom)){
    d_arith.setupAtom(atom);
  }
}

DeltaComputeCallback::DeltaComputeCallback(const TheoryArithPrivate& ta)
  : d_ta(ta)
{}
Rational DeltaComputeCallback::operator()() const{
  return d_ta.deltaValueForTotalOrder();
}

TempVarMalloc::TempVarMalloc(TheoryArithPrivate& ta)
: d_ta(ta)
{}
ArithVar TempVarMalloc::request(){
  Node skolem = mkRealSkolem("tmpVar");
  return d_ta.requestArithVar(skolem, false, true);
}
void TempVarMalloc::release(ArithVar v){
  d_ta.releaseArithVar(v);
}

BasicVarModelUpdateCallBack::BasicVarModelUpdateCallBack(TheoryArithPrivate& ta)
  : d_ta(ta)
{}
void BasicVarModelUpdateCallBack::operator()(ArithVar x){
  d_ta.signal(x);
}

RaiseConflict::RaiseConflict(TheoryArithPrivate& ta, ConstraintCPVec& buf )
  : d_ta(ta)
  , d_construction(buf)
{}

/* Adds a constraint to the constraint under construction. */
void RaiseConflict::addConstraint(ConstraintCP c){
  d_construction.push_back(c);
}
/* Turns the vector under construction into a conflict */
void RaiseConflict::commitConflict(){
  Assert(!d_construction.empty());
  sendConflict(d_construction);
  d_construction.clear();
}

void RaiseConflict::sendConflict(const ConstraintCPVec& vec){
  d_ta.raiseConflict(vec);
}

/* If you are not an equality engine, don't use this! */
void RaiseConflict::blackBoxConflict(Node n){
  d_ta.blackBoxConflict(n);
}


BoundCountingLookup::BoundCountingLookup(TheoryArithPrivate& ta)
: d_ta(ta)
{}

const BoundsInfo& BoundCountingLookup::boundsInfo(ArithVar basic) const{
  return d_ta.boundsInfo(basic);
}

BoundCounts BoundCountingLookup::atBounds(ArithVar basic) const{
  return boundsInfo(basic).atBounds();
}
BoundCounts BoundCountingLookup::hasBounds(ArithVar basic) const {
  return boundsInfo(basic).hasBounds();
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
