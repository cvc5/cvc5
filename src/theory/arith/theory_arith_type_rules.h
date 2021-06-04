/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {
namespace theory {
namespace arith {

class ArithConstantTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class ArithOperatorTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class RealNullaryOperatorTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class IAndOpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class IAndTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class IndexedRootPredicateTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__THEORY_ARITH_TYPE_RULES_H */
