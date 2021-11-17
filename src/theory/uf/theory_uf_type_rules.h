/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of UF.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__THEORY_UF_TYPE_RULES_H
#define CVC5__THEORY__UF__THEORY_UF_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5 {
namespace theory {
namespace uf {

class UfTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class CardinalityConstraintTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class CardinalityConstraintOpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class CombinedCardinalityConstraintTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class CombinedCardinalityConstraintOpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class PartialTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

// class with the typing rule for HO_APPLY terms
class HoApplyTypeRule
{
 public:
  // the typing rule for HO_APPLY terms
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class LambdaTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
  // computes whether a lambda is a constant value, via conversion to array
  // representation
  static bool computeIsConst(NodeManager* nodeManager, TNode n);
}; /* class LambdaTypeRule */

class FunctionProperties
{
 public:
  static Cardinality computeCardinality(TypeNode type);

  /** Function type is well-founded if its component sorts are */
  static bool isWellFounded(TypeNode type);
  /**
   * Ground term for function sorts is (lambda x. t) where x is the
   * canonical variable list for its type and t is the canonical ground term of
   * its range.
   */
  static Node mkGroundTerm(TypeNode type);
}; /* class FuctionProperties */

}  // namespace uf
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__UF__THEORY_UF_TYPE_RULES_H */
