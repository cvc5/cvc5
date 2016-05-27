/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for rationals and integers
 **
 ** Enumerators for rationals and integers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {
namespace theory {
namespace arith {

class RationalEnumerator : public TypeEnumeratorBase<RationalEnumerator> {
  Rational d_rat;

public:

  RationalEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw(AssertionException) :
    TypeEnumeratorBase<RationalEnumerator>(type),
    d_rat(0) {
    Assert(type.getKind() == kind::TYPE_CONSTANT &&
           type.getConst<TypeConstant>() == REAL_TYPE);
  }

  Node operator*() throw() {
    return NodeManager::currentNM()->mkConst(d_rat);
  }

  RationalEnumerator& operator++() throw() {
    // sequence is 0, then diagonal with negatives interleaved
    // ( 0, 1/1, -1/1, 2/1, -2/1, 1/2, -1/2, 3/1, -3/1, 1/3, -1/3,
    // 4/1, -4/1, 3/2, -3/2, 2/3, -2/3, 1/4, -1/4, ...)
    if(d_rat == 0) {
      d_rat = 1;
    } else if(d_rat < 0) {
      d_rat = -d_rat;
      Integer num = d_rat.getNumerator();
      Integer den = d_rat.getDenominator();
      do {
        num -= 1;
        den += 1;
        if(num == 0) {
          num = den;
          den = 1;
        }
        d_rat = Rational(num, den);
      } while(d_rat.getNumerator() != num);
    } else {
      d_rat = -d_rat;
    }
    return *this;
  }

  bool isFinished() throw() {
    return false;
  }

};/* class RationalEnumerator */

class IntegerEnumerator : public TypeEnumeratorBase<IntegerEnumerator> {
  Integer d_int;

public:

  IntegerEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw(AssertionException) :
    TypeEnumeratorBase<IntegerEnumerator>(type),
    d_int(0) {
    Assert(type.getKind() == kind::TYPE_CONSTANT &&
           type.getConst<TypeConstant>() == INTEGER_TYPE);
  }

  Node operator*() throw() {
    return NodeManager::currentNM()->mkConst(Rational(d_int));
  }

  IntegerEnumerator& operator++() throw() {
    // sequence is 0, 1, -1, 2, -2, 3, -3, ...
    if(d_int <= 0) {
      d_int = -d_int + 1;
    } else {
      d_int = -d_int;
    }
    return *this;
  }

  bool isFinished() throw() {
    return false;
  }

};/* class IntegerEnumerator */

class SubrangeEnumerator : public TypeEnumeratorBase<SubrangeEnumerator> {
  Integer d_int;
  SubrangeBounds d_bounds;
  bool d_direction;// true == +, false == -

public:

  SubrangeEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw(AssertionException) :
    TypeEnumeratorBase<SubrangeEnumerator>(type),
    d_int(0),
    d_bounds(type.getConst<SubrangeBounds>()),
    d_direction(d_bounds.lower.hasBound()) {

    d_int = d_direction ? d_bounds.lower.getBound() : d_bounds.upper.getBound();

    Assert(type.getKind() == kind::SUBRANGE_TYPE);

    // if we're counting down, there's no lower bound
    Assert(d_direction || !d_bounds.lower.hasBound());
  }

  Node operator*() throw(NoMoreValuesException) {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst(Rational(d_int));
  }

  SubrangeEnumerator& operator++() throw() {
    if(d_direction) {
      if(!d_bounds.upper.hasBound() || d_int <= d_bounds.upper.getBound()) {
        d_int += 1;
      }
    } else {
      // if we're counting down, there's no lower bound
      d_int -= 1;
    }
    return *this;
  }

  bool isFinished() throw() {
    // if we're counting down, there's no lower bound
    return d_direction &&
      d_bounds.upper.hasBound() &&
      d_int > d_bounds.upper.getBound();
  }

};/* class SubrangeEnumerator */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H */
