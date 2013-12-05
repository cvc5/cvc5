/*********************                                                        */
/*! \file callbacks.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

void SetupLiteralCallBack::operator()(TNode lit){
  TNode atom = (lit.getKind() == kind::NOT) ? lit[0] : lit;
  if(!d_arith.isSetup(atom)){
    d_arith.setupAtom(atom);
  }
}

Rational DeltaComputeCallback::operator()() const{
  return d_ta.deltaValueForTotalOrder();
}

ArithVar TempVarMalloc::request(){
  Node skolem = mkRealSkolem("tmpVar");
  return d_ta.requestArithVar(skolem, false);
}
void TempVarMalloc::release(ArithVar v){
  d_ta.releaseArithVar(v);
}

void BasicVarModelUpdateCallBack::operator()(ArithVar x){
  d_ta.signal(x);
}

void RaiseConflict::operator()(Node n){
  d_ta.raiseConflict(n);
}

const BoundsInfo& BoundCountingLookup::boundsInfo(ArithVar basic) const{
  return d_ta.boundsInfo(basic);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
