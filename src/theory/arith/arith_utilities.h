


#ifndef __CVC4__THEORY__ARITH__ARITH_UTILITIES_H
#define __CVC4__THEORY__ARITH__ARITH_UTILITIES_H


#include "util/rational.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arith {

inline Node mkRationalNode(Rational& q){
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
    k = LT;
    break;
  case GEQ:
    k = LEQ;
    break;
  case LEQ:
    k = GEQ;
    break;
  case LT:
    k = GT;
    break;
  default:
    Unreachable();
  }

  return NodeManager::currentNM()->mkNode(k, p[0],p[1]);
}

}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */



#endif /* __CVC4__THEORY__ARITH__ARITH_UTILITIES_H */
