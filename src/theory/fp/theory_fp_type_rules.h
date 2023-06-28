/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type rules for the theory of floating-point arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FP__THEORY_FP_TYPE_RULES_H
#define CVC5__THEORY__FP__THEORY_FP_TYPE_RULES_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {

class NodeManager;

namespace theory {
namespace fp {

/** Type rule for floating-point values. */
class FloatingPointConstantTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for roundingmode values. */
class RoundingModeConstantTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for (fp ...) operator. */
class FloatingPointFPTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for floating-point predicates to check if all arguments are
 * floating-points of the same sort.
 */
class FloatingPointTestTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for floating-point operators which expect that all operands are
 * floating-points to check if all operands are floating-points of the same
 * sort.
 */
class FloatingPointOperationTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for floating-point operators which expect a roundingmode as first
 * operand and floating-points for the remaining operands. Checks if the
 * floating-point operands are of the same sort.
 */
class FloatingPointRoundingOperationTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for floating-point partial operators (min, max) which expect that
 * all operands are floating-points to check if all operands are
 * floating-points of the same sort.
 */
class FloatingPointPartialOperationTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point to_fp conversion from IEEE bit-vector. */
class FloatingPointToFPIEEEBitVectorTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point to_fp conversion from floating-point. */
class FloatingPointToFPFloatingPointTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point to_fp conversion from real. */
class FloatingPointToFPRealTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point to_fp conversion from signed bit-vector. */
class FloatingPointToFPSignedBitVectorTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point to_fp conversion from unsigned bit-vector. */
class FloatingPointToFPUnsignedBitVectorTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for conversion from floating-point to unsigned bit-vector. */
class FloatingPointToUBVTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for conversion from floating-point to signed bit-vector. */
class FloatingPointToSBVTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for conversion from floating-point to unsigned bit-vector (total
 * version).
 */
class FloatingPointToUBVTotalTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);
  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/**
 * Type rule for conversion from floating-point to signed bit-vector (total
 * version).
 */
class FloatingPointToSBVTotalTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for conversion from floating-point to real. */
class FloatingPointToRealTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for conversion from floating-point to real (total version). */
class FloatingPointToRealTotalTypeRule
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point components of bit-width 1. */
class FloatingPointComponentBit
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point exponent component. */
class FloatingPointComponentExponent
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for floating-point significand component. */
class FloatingPointComponentSignificand
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Type rule for the ROUNDINGMODE_BITBLAST operator. */
class RoundingModeBitBlast
{
 public:
  static TypeNode preComputeType(NodeManager* nm, TNode n);

  static TypeNode computeType(NodeManager* nodeManager,
                              TNode n,
                              bool check,
                              std::ostream* errOut);
};

/** Cardinality computation for floating-point sorts. */
class CardinalityComputer
{
 public:
  static Cardinality computeCardinality(TypeNode type);
};

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal

#endif
