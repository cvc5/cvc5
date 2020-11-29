/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerators for rationals and integers
 **
 ** Enumerators for rationals and integers.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H
#define CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H

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
  RationalEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<RationalEnumerator>(type), d_rat(0)
  {
    Assert(type.getKind() == kind::TYPE_CONSTANT
           && type.getConst<TypeConstant>() == REAL_TYPE);
  }

  Node operator*() override { return NodeManager::currentNM()->mkConst(d_rat); }
  RationalEnumerator& operator++() override
  {
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

  bool isFinished() override { return false; }
};/* class RationalEnumerator */

class IntegerEnumerator : public TypeEnumeratorBase<IntegerEnumerator> {
  Integer d_int;

 public:
  IntegerEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<IntegerEnumerator>(type), d_int(0)
  {
    Assert(type.getKind() == kind::TYPE_CONSTANT
           && type.getConst<TypeConstant>() == INTEGER_TYPE);
  }

  Node operator*() override
  {
    return NodeManager::currentNM()->mkConst(Rational(d_int));
  }

  IntegerEnumerator& operator++() override
  {
    // sequence is 0, 1, -1, 2, -2, 3, -3, ...
    if(d_int <= 0) {
      d_int = -d_int + 1;
    } else {
      d_int = -d_int;
    }
    return *this;
  }

  bool isFinished() override { return false; }
};/* class IntegerEnumerator */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__TYPE_ENUMERATOR_H */
