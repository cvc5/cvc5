/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for theory arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H
#define CVC5__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * Type rule for arithmetic values.
 * Returns `integerType` or `realType` depending on the value.
 */
class ArithConstantTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for real algebraic numbers.
 * Returns `realType`.
 */
class ArithRealAlgebraicNumberOpTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for real algebraic numbers.
 * Returns `realType`.
 */
class ArithRealAlgebraicNumberTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for arithmetic relations. Returns Boolean. Throws a type error
 * if the types of the children are not arithmetic or not comparable.
 */
class ArithRelationTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for arithmetic operators.
 * Takes care of mixed-integer operators, cases and (total) division.
 */
class ArithOperatorTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for nullary real operators. */
class RealNullaryOperatorTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for the IAND kind.
 * Always returns integerType.
 */
class IAndTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for the POW2 operator.
 * Always returns integerType.
 */
class Pow2TypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for the IndexedRootPredicate operator.
 * Checks that the two arguments are booleanType and realType, always returns
 * booleanType.
 */
class IndexedRootPredicateTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H */
