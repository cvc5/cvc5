/*********************                                                        */
/*! \file theory_arrays_type_rules.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Typing and cardinality rules for the theory of arrays
 **
 ** Typing and cardinality rules for the theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace arrays {

struct ArraySelectTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::SELECT);
    TypeNode arrayType = n[0].getType(check);
    if( check ) {
      if(!arrayType.isArray()) {
        throw TypeCheckingExceptionPrivate(n, "array select operating on non-array");
      }
      TypeNode indexType = n[1].getType(check);
      if(!indexType.isSubtypeOf(arrayType.getArrayIndexType())){
        throw TypeCheckingExceptionPrivate(n, "array select not indexed with correct type for array");
      }
    }
    return arrayType.getArrayConstituentType();
  }
};/* struct ArraySelectTypeRule */

struct ArrayStoreTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::STORE);
    TypeNode arrayType = n[0].getType(check);
    if( check ) {
      if(!arrayType.isArray()) {
        throw TypeCheckingExceptionPrivate(n, "array store operating on non-array");
      }
      TypeNode indexType = n[1].getType(check);
      TypeNode valueType = n[2].getType(check);
      if(!indexType.isSubtypeOf(arrayType.getArrayIndexType())){
        throw TypeCheckingExceptionPrivate(n, "array store not indexed with correct type for array");
      }
      if(!valueType.isSubtypeOf(arrayType.getArrayConstituentType())){
	Debug("array-types") << "array type: "<< arrayType.getArrayConstituentType() << std::endl;
	Debug("array-types") << "value types: " << valueType << std::endl;
        throw TypeCheckingExceptionPrivate(n, "array store not assigned with correct type for array");
      }
    }
    return arrayType;
  }
};/* struct ArrayStoreTypeRule */

struct ArrayTableFunTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::ARR_TABLE_FUN);
    TypeNode arrayType = n[0].getType(check);
    if( check ) {
      if(!arrayType.isArray()) {
        throw TypeCheckingExceptionPrivate(n, "array table fun arg 0 is non-array");
      }
      TypeNode arrType2 = n[1].getType(check);
      if(!arrayType.isArray()) {
        throw TypeCheckingExceptionPrivate(n, "array table fun arg 1 is non-array");
      }
      TypeNode indexType = n[2].getType(check);
      if(!indexType.isSubtypeOf(arrayType.getArrayIndexType())){
        throw TypeCheckingExceptionPrivate(n, "array table fun arg 2 does not match type of array");
      }
      indexType = n[3].getType(check);
      if(!indexType.isSubtypeOf(arrayType.getArrayIndexType())){
        throw TypeCheckingExceptionPrivate(n, "array table fun arg 3 does not match type of array");
      }
    }
    return arrayType.getArrayIndexType();
  }
};/* struct ArrayStoreTypeRule */

struct CardinalityComputer {
  inline static Cardinality computeCardinality(TypeNode type) {
    Assert(type.getKind() == kind::ARRAY_TYPE);

    Cardinality indexCard = type[0].getCardinality();
    Cardinality valueCard = type[1].getCardinality();

    return valueCard ^ indexCard;
  }
};/* struct CardinalityComputer */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H */
