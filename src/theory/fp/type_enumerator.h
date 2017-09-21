/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Martin Brain
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2015  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An enumerator for floating-point numbers.
 **
 ** An enumerator for floating-point numbers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__FP__TYPE_ENUMERATOR_H

#include "util/floatingpoint.h"
#include "util/bitvector.h"
#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace fp {

class FloatingPointEnumerator : public TypeEnumeratorBase<FloatingPointEnumerator> {

  unsigned e;
  unsigned s;
  BitVector state;
  bool enumerationComplete;

protected :

  FloatingPoint createFP (void) const {
    // Rotate the LSB into the sign so that NaN is the last value
    BitVector value = state.logicalRightShift(1) | state.leftShift(state.getSize() - 1);
    
    return FloatingPoint(e, s, value);
  }


public:

  FloatingPointEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw(AssertionException) :
    TypeEnumeratorBase<FloatingPointEnumerator>(type),
      e(type.getFloatingPointExponentSize()),
      s(type.getFloatingPointSignificandSize()),
      state(e + s, 0U),
      enumerationComplete(false) 
    {}


  Node operator*() throw(NoMoreValuesException) {
    if (enumerationComplete) {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst(createFP());
  }

  FloatingPointEnumerator& operator++() throw() {
    FloatingPoint current(createFP());

    if (current.isNaN()) {
      enumerationComplete = true;
    } else {
      state = state + BitVector(state.getSize(), 1U);
    }

    return *this;
  }

  bool isFinished() throw() {
    return enumerationComplete;
  }

};/* FloatingPointEnumerator */

class RoundingModeEnumerator : public TypeEnumeratorBase<RoundingModeEnumerator> {

  RoundingMode rm;
  bool enumerationComplete;

public:

  RoundingModeEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw(AssertionException) :
    TypeEnumeratorBase<RoundingModeEnumerator>(type),
      rm(roundNearestTiesToEven),
      enumerationComplete(false)
    {}


  Node operator*() throw(NoMoreValuesException) {
    if (enumerationComplete) {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst(rm);
  }

  RoundingModeEnumerator& operator++() throw() {
    switch (rm) {
    case roundNearestTiesToEven : rm = roundTowardPositive; break;
    case roundTowardPositive : rm = roundTowardNegative; break;
    case roundTowardNegative : rm = roundTowardZero; break;
    case roundTowardZero : rm = roundNearestTiesToAway; break;
    case roundNearestTiesToAway : enumerationComplete = true; break;
    default : Unreachable("Unknown rounding mode?"); break;
    }
    return *this;
  }

  bool isFinished() throw() {
    return enumerationComplete;
  }

};/* RoundingModeEnumerator */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__TYPE_ENUMERATOR_H */
