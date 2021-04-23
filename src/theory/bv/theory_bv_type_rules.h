/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitvector theory typing rules.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_TYPE_RULES_H
#define CVC5__THEORY__BV__THEORY_BV_TYPE_RULES_H

#include "expr/node.h"

namespace cvc5 {

class TypeNode;

namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

class CardinalityComputer
{
 public:
  static Cardinality computeCardinality(TypeNode type);
};

/* -------------------------------------------------------------------------- */

class BitVectorConstantTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/* -------------------------------------------------------------------------- */

class BitVectorFixedWidthTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/* -------------------------------------------------------------------------- */

class BitVectorPredicateTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorUnaryPredicateTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorBVPredTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/* -------------------------------------------------------------------------- */
/* non-parameterized operator kinds                                           */
/* -------------------------------------------------------------------------- */

class BitVectorConcatTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorToBVTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    for (const auto& child : n)
    {
      TypeNode t = child.getType(check);
      if (!t.isBoolean())
      {
        throw TypeCheckingExceptionPrivate(n, "expecting Boolean terms");
      }
    }
    return nodeManager->mkBitVectorType(n.getNumChildren());
  }
};

class BitVectorITETypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/* -------------------------------------------------------------------------- */
/* parameterized operator kinds                                               */
/* -------------------------------------------------------------------------- */

class BitVectorBitOfTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorExtractTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorRepeatTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorExtendTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class IntToBitVectorOpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorConversionTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/* -------------------------------------------------------------------------- */
/* internal                                                                   */
/* -------------------------------------------------------------------------- */

class BitVectorEagerAtomTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorAckermanizationUdivTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

class BitVectorAckermanizationUremTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BV__THEORY_BV_TYPE_RULES_H */
