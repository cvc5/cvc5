/*********************                                                        */
/*! \file theory_arrays_type_rules.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of arrays.
 **
 ** Theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H_
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H_

namespace CVC4 {
namespace theory {
namespace arrays {

struct ArraySelectTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::SELECT);
    TypeNode arrayType = n[0].getType(check);
    if( check ) {
      TypeNode indexType = n[1].getType(check);
      if(arrayType.getArrayIndexType() != indexType) {
        throw TypeCheckingExceptionPrivate(n, "array select not indexed with correct type for array");
      }
    }
    return arrayType.getArrayConstituentType();
  }
};/* struct ArraySelectTypeRule */

struct ArrayStoreTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::STORE);
    TypeNode arrayType = n[0].getType(check);
    if( check ) {
      TypeNode indexType = n[1].getType(check);
      TypeNode valueType = n[2].getType(check);
      if(arrayType.getArrayIndexType() != indexType) {
        throw TypeCheckingExceptionPrivate(n, "array store not indexed with correct type for array");
      }
      if(arrayType.getArrayConstituentType() != valueType) {
        throw TypeCheckingExceptionPrivate(n, "array store not assigned with correct type for array");
      }
    }
    return arrayType;
  }
};/* struct ArrayStoreTypeRule */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H_ */
