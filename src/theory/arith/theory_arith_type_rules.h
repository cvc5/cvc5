/*********************                                                        */
/*! \file theory_arith_type_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters, cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add brief comments here ]]
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace arith {


class ArithConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate) {
    if (n.getKind() == kind::CONST_RATIONAL) return nodeManager->realType();
    return nodeManager->integerType();
  }
};

class ArithOperatorTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate) {
    TypeNode integerType = nodeManager->integerType();
    TypeNode realType = nodeManager->realType();
    TNode::iterator child_it = n.begin();
    TNode::iterator child_it_end = n.end();
    bool isInteger = true;
    for(; child_it != child_it_end; ++child_it) {
      TypeNode childType = (*child_it).getType(check);
      if (!childType.isInteger()) {
        isInteger = false;
        if( !check ) { // if we're not checking, nothing left to do
          break;
        }
      }
      if( check ) {
        if(childType != integerType && childType != realType) {
          throw TypeCheckingExceptionPrivate(n, "expecting an arithmetic subterm");
        }
      }
    }
    return (isInteger ? integerType : realType);
  }
};

class ArithPredicateTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate) {
    if( check ) {
      TypeNode integerType = nodeManager->integerType();
      TypeNode realType = nodeManager->realType();
      TypeNode lhsType = n[0].getType(check);
      if (lhsType != integerType && lhsType != realType) {
        throw TypeCheckingExceptionPrivate(n, "expecting an arithmetic term on the left-hand-side");
      }
      TypeNode rhsType = n[1].getType(check);
      if (rhsType != integerType && rhsType != realType) {
        throw TypeCheckingExceptionPrivate(n, "expecting an arithmetic term on the right-hand-side");
      }
    }
    return nodeManager->booleanType();
  }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H */
