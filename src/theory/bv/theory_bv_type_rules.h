/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

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
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/* -------------------------------------------------------------------------- */

class BitVectorFixedWidthTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/* -------------------------------------------------------------------------- */

class BitVectorPredicateTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorRedTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorBVPredTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/* -------------------------------------------------------------------------- */
/* non-parameterized operator kinds                                           */
/* -------------------------------------------------------------------------- */

class BitVectorConcatTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorToBVTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorITETypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/* -------------------------------------------------------------------------- */
/* parameterized operator kinds                                               */
/* -------------------------------------------------------------------------- */

class BitVectorBitOfTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorExtractTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorRepeatTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorExtendTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/* -------------------------------------------------------------------------- */
/* internal                                                                   */
/* -------------------------------------------------------------------------- */

class BitVectorEagerAtomTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorAckermanizationUdivTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

class BitVectorAckermanizationUremTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__THEORY_BV_TYPE_RULES_H */
