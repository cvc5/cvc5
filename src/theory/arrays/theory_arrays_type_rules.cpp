/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of arrays.
 */

#include "theory/arrays/theory_arrays_type_rules.h"

// for array-constant attributes
#include "expr/array_store_all.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/builtin/theory_builtin_type_rules.h"
#include "theory/type_enumerator.h"
#include "util/cardinality.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

TypeNode ArraySelectTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode ArraySelectTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check,
                                          std::ostream* errOut)
{
  Assert(n.getKind() == kind::SELECT);
  TypeNode arrayType = n[0].getTypeOrNull();
  if (check)
  {
    if (!arrayType.isMaybeKind(kind::ARRAY_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "array select operating on non-array";
      }
      return TypeNode::null();
    }
    TypeNode indexType = n[1].getTypeOrNull();
    if (!indexType.isComparableTo(arrayType.getArrayIndexType()))
    {
      if (errOut)
      {
        (*errOut) << "array select not indexed with correct type for array";
      }
      return TypeNode::null();
    }
  }
  if (arrayType.isAbstract())
  {
    // if selecting from a (fully) abstract array, the return is unknown.
    return nodeManager->mkAbstractType(kind::ABSTRACT_TYPE);
  }
  // otherwise
  return arrayType.getArrayConstituentType();
}

TypeNode ArrayStoreTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ArrayStoreTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check,
                                         std::ostream* errOut)
{
  if (n.getKind() == kind::STORE)
  {
    TypeNode arrayType = n[0].getTypeOrNull();
    if (check)
    {
      if (!arrayType.isMaybeKind(kind::ARRAY_TYPE))
      {
        if (errOut)
        {
          (*errOut) << "array store operating on non-array";
        }
        return TypeNode::null();
      }
    }
    TypeNode indexType = n[1].getTypeOrNull();
    TypeNode aindexType = arrayType.getArrayIndexType();
    TypeNode indexjoin = indexType.leastUpperBound(aindexType);
    if (indexjoin.isNull())
    {
      if (errOut)
      {
        (*errOut) << "array store not indexed with correct type for array";
      }
      return TypeNode::null();
    }
    TypeNode valueType = n[2].getTypeOrNull();
    TypeNode avalueType = arrayType.getArrayConstituentType();
    TypeNode valuejoin = valueType.leastUpperBound(avalueType);
    if (valuejoin.isNull())
    {
      if (errOut)
      {
        (*errOut) << "array store not assigned with correct type for array";
      }
      return TypeNode::null();
    }
    return NodeManager::currentNM()->mkArrayType(indexjoin, valuejoin);
  }
  else
  {
    Assert(n.getKind() == kind::STORE_ALL);
    ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
    return storeAll.getType();
  }
}

bool ArrayStoreTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == kind::STORE);

  TNode store = n[0];
  TNode index = n[1];
  TNode value = n[2];

  // A constant must have only constant children and be in normal form
  // If any child is non-const, this is not a constant
  if (!store.isConst() || !index.isConst() || !value.isConst())
  {
    return false;
  }

  // Normal form for nested stores is just ordering by index but also need to
  // check that we are not writing to default value
  if (store.getKind() == kind::STORE && (!(store[1] < index)))
  {
    return false;
  }

  unsigned depth = 1;
  unsigned valCount = 1;
  while (store.getKind() == kind::STORE)
  {
    depth += 1;
    if (store[2] == value)
    {
      valCount += 1;
    }
    store = store[0];
  }
  Assert(store.getKind() == kind::STORE_ALL);
  ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
  Node defaultValue = storeAll.getValue();
  if (value == defaultValue)
  {
    return false;
  }

  TypeNode itype = index.getType();
  CardinalityClass itcc = itype.getCardinalityClass();

  if (itcc != CardinalityClass::FINITE && itcc != CardinalityClass::ONE)
  {
    return true;
  }

  // Get the cardinality of the index type
  Cardinality indexCard = itype.getCardinality();

  if (indexCard.isInfinite())
  {
    return true;
  }

  // When index sort is finite, we have to check whether there is any value
  // that is written to more than the default value.  If so, it is not in
  // normal form.

  // Get the most frequently written value for n[0]
  TNode mostFrequentValue;
  unsigned mostFrequentValueCount = 0;
  store = n[0];
  if (store.getKind() == kind::STORE)
  {
    mostFrequentValue = getMostFrequentValue(store);
    mostFrequentValueCount = getMostFrequentValueCount(store);
  }

  // Compute the most frequently written value for n
  if (valCount > mostFrequentValueCount
      || (valCount == mostFrequentValueCount && value < mostFrequentValue))
  {
    mostFrequentValue = value;
    mostFrequentValueCount = valCount;
  }

  // Need to make sure the default value count is larger, or the same and the
  // default value is expression-order-less-than nextValue
  Cardinality::CardinalityComparison compare =
      indexCard.compare(mostFrequentValueCount + depth);
  Assert(compare != Cardinality::UNKNOWN);
  if (compare == Cardinality::LESS
      || (compare == Cardinality::EQUAL
          && (!(defaultValue < mostFrequentValue))))
  {
    return false;
  }
  setMostFrequentValue(n, mostFrequentValue);
  setMostFrequentValueCount(n, mostFrequentValueCount);
  return true;
}

TypeNode ArrayLambdaTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ArrayLambdaTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check,
                                          std::ostream* errOut)
{
  Assert(n.getKind() == kind::ARRAY_LAMBDA);
  TypeNode lamType = n[0].getTypeOrNull();
  if (check)
  {
    if (n[0].getKind() != kind::LAMBDA)
    {
      if (errOut)
      {
        (*errOut) << "array lambda arg is non-lambda";
      }
      return TypeNode::null();
    }
  }
  if (lamType.getNumChildren() != 2)
  {
    if (errOut)
    {
      (*errOut) << "array lambda arg is not unary lambda";
    }
    return TypeNode::null();
  }
  return nodeManager->mkArrayType(lamType[0], lamType[1]);
}

Cardinality ArraysProperties::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == kind::ARRAY_TYPE);

  Cardinality indexCard = type[0].getCardinality();
  Cardinality valueCard = type[1].getCardinality();

  return valueCard ^ indexCard;
}

bool ArraysProperties::isWellFounded(TypeNode type)
{
  return type[0].isWellFounded() && type[1].isWellFounded();
}

Node ArraysProperties::mkGroundTerm(TypeNode type)
{
  Assert(type.getKind() == kind::ARRAY_TYPE);
  NodeManager* nm = NodeManager::currentNM();
  TypeNode elemType = type.getArrayConstituentType();
  Node elem = nm->mkGroundTerm(elemType);
  if (elem.isConst())
  {
    return NodeManager::currentNM()->mkConst(ArrayStoreAll(type, elem));
  }
  // Note the distinction between mkGroundTerm and mkGroundValue. While
  // an arbitrary value can be obtained by calling the type enumerator here,
  // that is wrong for types that are not closed enumerable since it may
  // return a term containing values that should not appear in e.g. assertions.
  // For example, arrays whose element type is an uninterpreted sort will
  // incorrectly introduce uninterpreted sort values if this is done.
  // It is currently infeasible to construct an ArrayStoreAll with the element
  // type's mkGroundTerm as an argument when that term is not constant.
  // Thus, we must simply return a fresh Skolem here, using the same utility
  // as that of uninterpreted sorts.
  return builtin::SortProperties::mkGroundTerm(type);
}

TypeNode ArrayEqRangeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}

TypeNode ArrayEqRangeTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == kind::EQ_RANGE);
  if (check)
  {
    TypeNode n0_type = n[0].getTypeOrNull();
    TypeNode n1_type = n[1].getTypeOrNull();
    if (!n0_type.isMaybeKind(kind::ARRAY_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "first operand of eqrange is not an array";
      }
      return TypeNode::null();
    }
    if (!n1_type.isMaybeKind(kind::ARRAY_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "second operand of eqrange is not an array";
      }
      return TypeNode::null();
    }
    if (!n0_type.isComparableTo(n1_type))
    {
      if (errOut)
      {
        (*errOut) << "array types do not match";
      }
      return TypeNode::null();
    }
    TypeNode indexType = n0_type.getArrayIndexType();
    TypeNode indexRangeType1 = n[2].getTypeOrNull();
    TypeNode indexRangeType2 = n[3].getTypeOrNull();
    if (!indexRangeType1.isComparableTo(indexType))
    {
      if (errOut)
      {
        (*errOut) << "eqrange lower index type does not match array index type";
      }
      return TypeNode::null();
    }
    if (!indexRangeType2.isComparableTo(indexType))
    {
      if (errOut)
      {
        (*errOut) << "eqrange upper index type does not match array index type";
      }
      return TypeNode::null();
    }
    if (!indexType.isMaybeKind(kind::BITVECTOR_TYPE)
        && !indexType.isMaybeKind(kind::FLOATINGPOINT_TYPE)
        && !indexType.isRealOrInt())
    {
      if (errOut)
      {
        (*errOut) << "eqrange only supports bit-vectors, floating-points, "
                     "integers, and reals as index type";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal
