/*********************                                                        */
/*! \file arith_utilities.h
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_UTILITIES_H
#define __CVC4__THEORY__ARITH__ARITH_UTILITIES_H

#include "util/rational.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {

inline Node mkRationalNode(const Rational& q){
  return NodeManager::currentNM()->mkConst<Rational>(q);
}

inline Node mkBoolNode(bool b){
  return NodeManager::currentNM()->mkConst<bool>(b);
}



inline Rational coerceToRational(TNode constant){
  switch(constant.getKind()){
  case kind::CONST_INTEGER:
    {
      Rational q(constant.getConst<Integer>());
      return q;
    }
  case kind::CONST_RATIONAL:
    return constant.getConst<Rational>();
  default:
    Unreachable();
  }
  Rational unreachable(0,0);
  return unreachable;
}

inline Node coerceToRationalNode(TNode constant){
  switch(constant.getKind()){
  case kind::CONST_INTEGER:
    {
      Rational q(constant.getConst<Integer>());
      Node n = mkRationalNode(q);
      return n;
    }
  case kind::CONST_RATIONAL:
    return constant;
  default:
    Unreachable();
  }
  return Node::null();
}



/** is k \in {LT, LEQ, EQ, GEQ, GT} */
inline bool isRelationOperator(Kind k){
  using namespace kind;

  switch(k){
  case LT:
  case LEQ:
  case EQUAL:
  case GEQ:
  case GT:
    return true;
  default:
    return false;
  }
}

/** is k \in {LT, LEQ, EQ, GEQ, GT} */
inline Kind negateRelationKind(Kind k){
  using namespace kind;

  switch(k){
  case LT: return GT;
  case LEQ: return GEQ;
  case EQUAL: return EQUAL;
  case GEQ: return LEQ;
  case GT: return LT;

  default:
    Unreachable();
  }
}
inline bool evaluateConstantPredicate(Kind k, const Rational& left, const Rational& right){
  using namespace kind;

  switch(k){
  case LT:    return left <  right;
  case LEQ:   return left <= right;
  case EQUAL: return left == right;
  case GEQ:   return left >= right;
  case GT:    return left >  right;
  default:
    Unreachable();
    return true;
  }
}



inline Node pushInNegation(Node assertion){
  using namespace CVC4::kind;
  Assert(assertion.getKind() == NOT);

  Node p = assertion[0];

  Kind k;

  switch(p.getKind()){
  case EQUAL:
    return assertion;
  case GT:
    k = LEQ;
    break;
  case GEQ:
    k = LT;
    break;
  case LEQ:
    k = GT;
    break;
  case LT:
    k = GEQ;
    break;
  default:
    Unreachable();
  }

  return NodeManager::currentNM()->mkNode(k, p[0],p[1]);
}

/**
 * Validates that a node constraint has the following form:
 *   constraint: x |><| c
 * where |><| is either <, <=, ==, >=, LT,
 * x is of metakind a variabale,
 * and c is a constant rational.
 */
inline bool validateConstraint(TNode constraint){
  using namespace CVC4::kind;
  switch(constraint.getKind()){
  case LT:case LEQ: case EQUAL: case GEQ: case GT: break;
  default: return false;
  }

  if(constraint[0].getMetaKind() != metakind::VARIABLE) return false;
  return constraint[1].getKind() == CONST_RATIONAL;
}

inline int deltaCoeff(Kind k){
  switch(k){
  case kind::LT:
    return -1;
  case kind::GT:
    return 1;
  default:
    return 0;
  }
}

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



#endif /* __CVC4__THEORY__ARITH__ARITH_UTILITIES_H */
