/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {

class NodeManager;

namespace theory {
namespace fp {

/** Type rule for floating-point values. */
class FloatingPointConstantTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for roundingmode values. */
class RoundingModeConstantTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for (fp ...) operator. */
class FloatingPointFPTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for floating-point predicates to check if all arguments are
 * floating-points of the same sort.
 */
class FloatingPointTestTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for floating-point operators which expect that all operands are
 * floating-points to check if all operands are floating-points of the same
 * sort.
 */
class FloatingPointOperationTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for floating-point operators which expect a roundingmode as first
 * operand and floating-points for the remaining operands. Checks if the
 * floating-point operands are of the same sort.
 */
class FloatingPointRoundingOperationTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for floating-point partial operators (min, max) which expect that
 * all operands are floating-points to check if all operands are
 * floating-points of the same sort.
 */
class FloatingPointPartialOperationTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for floating-point parametric operators (to_fp, to_fp_unsigned)
 * which expect that all operands are floating-points to check if all operands
 * are floating-points of the same sort.
 */
class FloatingPointParametricOpTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point to_fp conversion from IEEE bit-vector. */
class FloatingPointToFPIEEEBitVectorTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point to_fp conversion from floating-point. */
class FloatingPointToFPFloatingPointTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point to_fp conversion from real. */
class FloatingPointToFPRealTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point to_fp conversion from signed bit-vector. */
class FloatingPointToFPSignedBitVectorTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point to_fp conversion from unsigned bit-vector. */
class FloatingPointToFPUnsignedBitVectorTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Generic type rule for floating-point to_fp conversion. */
class FloatingPointToFPGenericTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for conversion from floating-point to unsigned bit-vector. */
class FloatingPointToUBVTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for conversion from floating-point to signed bit-vector. */
class FloatingPointToSBVTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for conversion from floating-point to unsigned bit-vector (total
 * version).
 */
class FloatingPointToUBVTotalTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/**
 * Type rule for conversion from floating-point to signed bit-vector (total
 * version).
 */
class FloatingPointToSBVTotalTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for conversion from floating-point to real. */
class FloatingPointToRealTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for conversion from floating-point to real (total version). */
class FloatingPointToRealTotalTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point components of bit-width 1. */
class FloatingPointComponentBit
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point exponent component. */
class FloatingPointComponentExponent
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for floating-point significand component. */
class FloatingPointComponentSignificand
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Type rule for the ROUNDINGMODE_BITBLAST operator. */
class RoundingModeBitBlast
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check);
};

/** Cardinality computation for floating-point sorts. */
class CardinalityComputer
{
 public:
  static Cardinality computeCardinality(TypeNode type);
};

}  // namespace fp
}  // namespace theory
}  // namespace cvc5

#endif
