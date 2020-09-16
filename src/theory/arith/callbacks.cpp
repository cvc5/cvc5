/*********************                                                        */
/*! \file callbacks.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/callbacks.h"

#include "theory/arith/proof_macros.h"
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

RaiseConflict::RaiseConflict(TheoryArithPrivate& ta)
  : d_ta(ta)
{}

void RaiseConflict::raiseConflict(ConstraintCP c) const{
  Assert(c->inConflict());
  d_ta.raiseConflict(c);
}

FarkasConflictBuilder::FarkasConflictBuilder()
  : d_farkas()
  , d_constraints()
  , d_consequent(NullConstraint)
  , d_consequentSet(false)
{
  reset();
}

bool FarkasConflictBuilder::underConstruction() const{
  return d_consequent != NullConstraint;
}

bool FarkasConflictBuilder::consequentIsSet() const{
  return d_consequentSet;
}

void FarkasConflictBuilder::reset(){
  d_consequent = NullConstraint;
  d_constraints.clear();
  d_consequentSet = false;
  ARITH_PROOF(d_farkas.clear());
  Assert(!underConstruction());
}

/* Adds a constraint to the constraint under construction. */
void FarkasConflictBuilder::addConstraint(ConstraintCP c, const Rational& fc){
  Assert(
      !ARITH_PROOF_ON()
      || (!underConstruction() && d_constraints.empty() && d_farkas.empty())
      || (underConstruction() && d_constraints.size() + 1 == d_farkas.size()));
  Assert(ARITH_PROOF_ON() || d_farkas.empty());
  Assert(c->isTrue());

  if(d_consequent == NullConstraint){
    d_consequent = c;
  } else {
    d_constraints.push_back(c);
  }
  ARITH_PROOF(d_farkas.push_back(fc));
  Assert(!ARITH_PROOF_ON() || d_constraints.size() + 1 == d_farkas.size());
  Assert(ARITH_PROOF_ON() || d_farkas.empty());
}

void FarkasConflictBuilder::addConstraint(ConstraintCP c, const Rational& fc, const Rational& mult){
  Assert(!mult.isZero());
  if (ARITH_PROOF_ON() && !mult.isOne())
  {
    Rational prod = fc * mult;
    addConstraint(c, prod);
  }
  else
  {
    addConstraint(c, fc);
  }
}

void FarkasConflictBuilder::makeLastConsequent(){
  Assert(!d_consequentSet);
  Assert(underConstruction());

  if(d_constraints.empty()){
    // no-op
    d_consequentSet = true;
  } else {
    Assert(d_consequent != NullConstraint);
    ConstraintCP last = d_constraints.back();
    d_constraints.back() = d_consequent;
    d_consequent = last;
    ARITH_PROOF(std::swap(d_farkas.front(), d_farkas.back()));
    d_consequentSet = true;
  }

  Assert(!d_consequent->negationHasProof());
  Assert(d_consequentSet);
}

/* Turns the vector under construction into a conflict */
ConstraintCP FarkasConflictBuilder::commitConflict(){
  Assert(underConstruction());
  Assert(!d_constraints.empty());
  Assert(
      !ARITH_PROOF_ON()
      || (!underConstruction() && d_constraints.empty() && d_farkas.empty())
      || (underConstruction() && d_constraints.size() + 1 == d_farkas.size()));
  Assert(ARITH_PROOF_ON() || d_farkas.empty());
  Assert(d_consequentSet);

  ConstraintP not_c = d_consequent->getNegation();
  RationalVectorCP coeffs = ARITH_NULLPROOF(&d_farkas);
  not_c->impliedByFarkas(d_constraints, coeffs, true );

  reset();
  Assert(!underConstruction());
  Assert(not_c->inConflict());
  Assert(!d_consequentSet);
  return not_c;
}

RaiseEqualityEngineConflict::RaiseEqualityEngineConflict(TheoryArithPrivate& ta)
  : d_ta(ta)
{}

/* If you are not an equality engine, don't use this! */
void RaiseEqualityEngineConflict::raiseEEConflict(Node n) const{
  d_ta.raiseBlackBoxConflict(n);
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
