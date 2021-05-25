/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Clark Barrett, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of arrays.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H
#define CVC5__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace arrays {

struct ArraySelectTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct ArrayStoreTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);

  static bool computeIsConst(NodeManager* nodeManager, TNode n);
};

struct ArrayTableFunTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct ArrayLambdaTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct ArraysProperties
{
  static Cardinality computeCardinality(TypeNode type);

  static bool isWellFounded(TypeNode type);

  static Node mkGroundTerm(TypeNode type);
};

struct ArrayPartialSelectTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

struct ArrayEqRangeTypeRule
{
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARRAYS__THEORY_ARRAYS_TYPE_RULES_H */
