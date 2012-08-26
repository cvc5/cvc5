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

#include "theory/arrays/theory_arrays_rewriter.h" // for array-constant attributes

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
    if (n.getKind() == kind::STORE) {
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
    else {
      Assert(n.getKind() == kind::STORE_ALL);
      ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
      ArrayType arrayType = storeAll.getType();
      return TypeNode::fromType(arrayType);
    }
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
    throw (AssertionException) {
    Assert(n.getKind() == kind::STORE);
    NodeManagerScope nms(nodeManager);

    TNode store = n[0];
    TNode index = n[1];
    TNode value = n[2];

    // A constant must have only constant children and be in normal form
    // If any child is non-const, this is not a constant
    if (!store.isConst() || !index.isConst() || !value.isConst()) {
      return false;
    }

    // Normal form for nested stores is just ordering by index but also need to check that we are not writing
    // to default value
    if (store.getKind() == kind::STORE && (!(store[1] < index))) {
      return false;
    }

    unsigned depth = 1;
    unsigned valCount = 1;
    while (store.getKind() == kind::STORE) {
      depth += 1;
      if (store[2] == value) {
        valCount += 1;
      }
      store = store[0];
    }
    Assert(store.getKind() == kind::STORE_ALL);
    ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
    Node defaultValue = Node::fromExpr(storeAll.getExpr());
    if (value == defaultValue) {
      return false;
    }

    // Get the cardinality of the index type
    Cardinality indexCard = index.getType().getCardinality();

    if (indexCard.isInfinite()) {
      return true;
    }

    // When index sort is finite, we have to check whether there is any value
    // that is written to more than the default value.  If so, it is not in
    // normal form.

    // Get the most frequently written value for n[0]
    TNode mostFrequentValue;
    unsigned mostFrequentValueCount = 0;
    store = n[0];
    if (store.getKind() == kind::STORE) {
      mostFrequentValue = store.getAttribute(ArrayConstantMostFrequentValueAttr());
      mostFrequentValueCount = store.getAttribute(ArrayConstantMostFrequentValueCountAttr());
    }

    // Compute the most frequently written value for n
    if (valCount > mostFrequentValueCount ||
        (valCount == mostFrequentValueCount && value < mostFrequentValue)) {
      mostFrequentValue = value;
      mostFrequentValueCount = valCount;
    }

    // Need to make sure the default value count is larger, or the same and the default value is expression-order-less-than nextValue
    Cardinality::CardinalityComparison compare = indexCard.compare(mostFrequentValueCount + depth);
    Assert(compare != Cardinality::UNKNOWN);
    if (compare == Cardinality::LESS ||
        (compare == Cardinality::EQUAL && (!(defaultValue < mostFrequentValue)))) {
      return false;
    }
    n.setAttribute(ArrayConstantMostFrequentValueAttr(), mostFrequentValue);
    n.setAttribute(ArrayConstantMostFrequentValueCountAttr(), mostFrequentValueCount);
    return true;
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
};/* struct ArrayTableFunTypeRule */

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
