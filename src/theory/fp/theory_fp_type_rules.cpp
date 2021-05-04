/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Tim King
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

#include "theory/fp/theory_fp_type_rules.h"

// This is only needed for checking that components are only applied to leaves.
#include "theory/theory.h"
#include "util/roundingmode.h"

namespace cvc5 {
namespace theory {
namespace fp {

#define TRACE(FUNCTION)                                                \
  Trace("fp-type") << FUNCTION "::computeType(" << check << "): " << n \
                   << std::endl

TypeNode FloatingPointConstantTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
{
  TRACE("FloatingPointConstantTypeRule");

  const FloatingPoint& f = n.getConst<FloatingPoint>();

  if (check)
  {
    if (!(validExponentSize(f.getSize().exponentWidth())))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "constant with invalid exponent size");
    }
    if (!(validSignificandSize(f.getSize().significandWidth())))
    {
      throw TypeCheckingExceptionPrivate(
          n, "constant with invalid significand size");
    }
  }
  return nodeManager->mkFloatingPointType(f.getSize());
}

TypeNode RoundingModeConstantTypeRule::computeType(NodeManager* nodeManager,
                                                   TNode n,
                                                   bool check)
{
  TRACE("RoundingModeConstantTypeRule");

  // Nothing to check!
  return nodeManager->roundingModeType();
}

TypeNode FloatingPointFPTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check)
{
  TRACE("FloatingPointFPTypeRule");

  TypeNode signType = n[0].getType(check);
  TypeNode exponentType = n[1].getType(check);
  TypeNode significandType = n[2].getType(check);

  if (!signType.isBitVector() || !exponentType.isBitVector()
      || !significandType.isBitVector())
  {
    throw TypeCheckingExceptionPrivate(n,
                                       "arguments to fp must be bit vectors");
  }

  uint32_t signBits = signType.getBitVectorSize();
  uint32_t exponentBits = exponentType.getBitVectorSize();
  uint32_t significandBits = significandType.getBitVectorSize();

  if (check)
  {
    if (signBits != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "sign bit vector in fp must be 1 bit long");
    }
    else if (!(validExponentSize(exponentBits)))
    {
      throw TypeCheckingExceptionPrivate(
          n, "exponent bit vector in fp is an invalid size");
    }
    else if (!(validSignificandSize(significandBits)))
    {
      throw TypeCheckingExceptionPrivate(
          n, "significand bit vector in fp is an invalid size");
    }
  }

  // The +1 is for the implicit hidden bit
  return nodeManager->mkFloatingPointType(exponentBits, significandBits + 1);
}

TypeNode FloatingPointTestTypeRule::computeType(NodeManager* nodeManager,
                                                TNode n,
                                                bool check)
{
  TRACE("FloatingPointTestTypeRule");

  if (check)
  {
    TypeNode firstOperand = n[0].getType(check);

    if (!firstOperand.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(
          n, "floating-point test applied to a non floating-point sort");
    }

    size_t children = n.getNumChildren();
    for (size_t i = 1; i < children; ++i)
    {
      if (!(n[i].getType(check) == firstOperand))
      {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point test applied to mixed sorts");
      }
    }
  }

  return nodeManager->booleanType();
}

TypeNode FloatingPointOperationTypeRule::computeType(NodeManager* nodeManager,
                                                     TNode n,
                                                     bool check)
{
  TRACE("FloatingPointOperationTypeRule");

  TypeNode firstOperand = n[0].getType(check);

  if (check)
  {
    if (!firstOperand.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(
          n, "floating-point operation applied to a non floating-point sort");
    }

    size_t children = n.getNumChildren();
    for (size_t i = 1; i < children; ++i)
    {
      if (!(n[i].getType(check) == firstOperand))
      {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point test applied to mixed sorts");
      }
    }
  }

  return firstOperand;
}

TypeNode FloatingPointRoundingOperationTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointRoundingOperationTypeRule");

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }
  }

  TypeNode firstOperand = n[1].getType(check);

  if (check)
  {
    if (!firstOperand.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(
          n, "floating-point operation applied to a non floating-point sort");
    }

    size_t children = n.getNumChildren();
    for (size_t i = 2; i < children; ++i)
    {
      if (!(n[i].getType(check) == firstOperand))
      {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point operation applied to mixed sorts");
      }
    }
  }

  return firstOperand;
}

TypeNode FloatingPointPartialOperationTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointOperationTypeRule");
  AlwaysAssert(n.getNumChildren() > 0);

  TypeNode firstOperand = n[0].getType(check);

  if (check)
  {
    if (!firstOperand.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(
          n, "floating-point operation applied to a non floating-point sort");
    }

    const size_t children = n.getNumChildren();
    for (size_t i = 1; i < children - 1; ++i)
    {
      if (n[i].getType(check) != firstOperand)
      {
        throw TypeCheckingExceptionPrivate(
            n, "floating-point partial operation applied to mixed sorts");
      }
    }

    TypeNode UFValueType = n[children - 1].getType(check);

    if (!(UFValueType.isBitVector()) || !(UFValueType.getBitVectorSize() == 1))
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "floating-point partial operation final argument must be a "
          "bit-vector of length 1");
    }
  }

  return firstOperand;
}

TypeNode FloatingPointParametricOpTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointParametricOpTypeRule");

  return nodeManager->builtinOperatorType();
}

TypeNode FloatingPointToFPIEEEBitVectorTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointToFPIEEEBitVectorTypeRule");
  AlwaysAssert(n.getNumChildren() == 1);

  FloatingPointToFPIEEEBitVector info =
      n.getOperator().getConst<FloatingPointToFPIEEEBitVector>();

  if (check)
  {
    TypeNode operandType = n[0].getType(check);

    if (!(operandType.isBitVector()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to floating-point from "
                                         "bit vector used with sort other "
                                         "than bit vector");
    }
    else if (!(operandType.getBitVectorSize()
               == info.getSize().exponentWidth()
                      + info.getSize().significandWidth()))
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "conversion to floating-point from bit vector used with bit vector "
          "length that does not match floating point parameters");
    }
  }

  return nodeManager->mkFloatingPointType(info.getSize());
}

TypeNode FloatingPointToFPFloatingPointTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointToFPFloatingPointTypeRule");
  AlwaysAssert(n.getNumChildren() == 2);

  FloatingPointToFPFloatingPoint info =
      n.getOperator().getConst<FloatingPointToFPFloatingPoint>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isFloatingPoint()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to floating-point from "
                                         "floating-point used with sort "
                                         "other than floating-point");
    }
  }

  return nodeManager->mkFloatingPointType(info.getSize());
}

TypeNode FloatingPointToFPRealTypeRule::computeType(NodeManager* nodeManager,
                                                    TNode n,
                                                    bool check)
{
  TRACE("FloatingPointToFPRealTypeRule");
  AlwaysAssert(n.getNumChildren() == 2);

  FloatingPointToFPReal info =
      n.getOperator().getConst<FloatingPointToFPReal>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isReal()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to floating-point from "
                                         "real used with sort other than "
                                         "real");
    }
  }

  return nodeManager->mkFloatingPointType(info.getSize());
}

TypeNode FloatingPointToFPSignedBitVectorTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointToFPSignedBitVectorTypeRule");
  AlwaysAssert(n.getNumChildren() == 2);

  FloatingPointToFPSignedBitVector info =
      n.getOperator().getConst<FloatingPointToFPSignedBitVector>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isBitVector()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to floating-point from "
                                         "signed bit vector used with sort "
                                         "other than bit vector");
    }
  }

  return nodeManager->mkFloatingPointType(info.getSize());
}

TypeNode FloatingPointToFPUnsignedBitVectorTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointToFPUnsignedBitVectorTypeRule");
  AlwaysAssert(n.getNumChildren() == 2);

  FloatingPointToFPUnsignedBitVector info =
      n.getOperator().getConst<FloatingPointToFPUnsignedBitVector>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isBitVector()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to floating-point from "
                                         "unsigned bit vector used with sort "
                                         "other than bit vector");
    }
  }

  return nodeManager->mkFloatingPointType(info.getSize());
}

TypeNode FloatingPointToFPGenericTypeRule::computeType(NodeManager* nodeManager,
                                                       TNode n,
                                                       bool check)
{
  TRACE("FloatingPointToFPGenericTypeRule");

  FloatingPointToFPGeneric info =
      n.getOperator().getConst<FloatingPointToFPGeneric>();

  if (check)
  {
    uint32_t nchildren = n.getNumChildren();
    if (nchildren == 1)
    {
      if (!n[0].getType(check).isBitVector())
      {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a bit-vector");
      }
    }
    else
    {
      Assert(nchildren == 2);
      if (!n[0].getType(check).isRoundingMode())
      {
        throw TypeCheckingExceptionPrivate(
            n, "first argument must be a roundingmode");
      }
      TypeNode tn = n[1].getType(check);
      if (!tn.isBitVector() && !tn.isFloatingPoint() && !tn.isReal())
      {
        throw TypeCheckingExceptionPrivate(
            n, "second argument must be a bit-vector, floating-point or Real");
      }
    }
  }
  return nodeManager->mkFloatingPointType(info.getSize());
}

TypeNode FloatingPointToUBVTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check)
{
  TRACE("FloatingPointToUBVTypeRule");
  AlwaysAssert(n.getNumChildren() == 2);

  FloatingPointToUBV info = n.getOperator().getConst<FloatingPointToUBV>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isFloatingPoint()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to unsigned bit vector "
                                         "used with a sort other than "
                                         "floating-point");
    }
  }

  return nodeManager->mkBitVectorType(info.d_bv_size);
}

TypeNode FloatingPointToSBVTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check)
{
  TRACE("FloatingPointToSBVTypeRule");
  AlwaysAssert(n.getNumChildren() == 2);

  FloatingPointToSBV info = n.getOperator().getConst<FloatingPointToSBV>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isFloatingPoint()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to signed bit vector "
                                         "used with a sort other than "
                                         "floating-point");
    }
  }

  return nodeManager->mkBitVectorType(info.d_bv_size);
}

TypeNode FloatingPointToUBVTotalTypeRule::computeType(NodeManager* nodeManager,
                                                      TNode n,
                                                      bool check)
{
  TRACE("FloatingPointToUBVTotalTypeRule");
  AlwaysAssert(n.getNumChildren() == 3);

  FloatingPointToUBVTotal info =
      n.getOperator().getConst<FloatingPointToUBVTotal>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isFloatingPoint()))
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "conversion to unsigned bit vector total"
          "used with a sort other than "
          "floating-point");
    }

    TypeNode defaultValueType = n[2].getType(check);

    if (!(defaultValueType.isBitVector())
        || !(defaultValueType.getBitVectorSize() == info))
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "conversion to unsigned bit vector total"
          "needs a bit vector of the same length"
          "as last argument");
    }
  }

  return nodeManager->mkBitVectorType(info.d_bv_size);
}

TypeNode FloatingPointToSBVTotalTypeRule::computeType(NodeManager* nodeManager,
                                                      TNode n,
                                                      bool check)
{
  TRACE("FloatingPointToSBVTotalTypeRule");
  AlwaysAssert(n.getNumChildren() == 3);

  FloatingPointToSBVTotal info =
      n.getOperator().getConst<FloatingPointToSBVTotal>();

  if (check)
  {
    TypeNode roundingModeType = n[0].getType(check);

    if (!roundingModeType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument must be a rounding mode");
    }

    TypeNode operandType = n[1].getType(check);

    if (!(operandType.isFloatingPoint()))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to signed bit vector "
                                         "used with a sort other than "
                                         "floating-point");
    }

    TypeNode defaultValueType = n[2].getType(check);

    if (!(defaultValueType.isBitVector())
        || !(defaultValueType.getBitVectorSize() == info))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "conversion to signed bit vector total"
                                         "needs a bit vector of the same length"
                                         "as last argument");
    }
  }

  return nodeManager->mkBitVectorType(info.d_bv_size);
}

TypeNode FloatingPointToRealTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check)
{
  TRACE("FloatingPointToRealTypeRule");
  AlwaysAssert(n.getNumChildren() == 1);

  if (check)
  {
    TypeNode operandType = n[0].getType(check);

    if (!operandType.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(
          n, "floating-point to real applied to a non floating-point sort");
    }
  }

  return nodeManager->realType();
}

TypeNode FloatingPointToRealTotalTypeRule::computeType(NodeManager* nodeManager,
                                                       TNode n,
                                                       bool check)
{
  TRACE("FloatingPointToRealTotalTypeRule");
  AlwaysAssert(n.getNumChildren() == 2);

  if (check)
  {
    TypeNode operandType = n[0].getType(check);

    if (!operandType.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "floating-point to real total applied to a non floating-point sort");
    }

    TypeNode defaultValueType = n[1].getType(check);

    if (!defaultValueType.isReal())
    {
      throw TypeCheckingExceptionPrivate(
          n, "floating-point to real total needs a real second argument");
    }
  }

  return nodeManager->realType();
}

TypeNode FloatingPointComponentBit::computeType(NodeManager* nodeManager,
                                                TNode n,
                                                bool check)
{
  TRACE("FloatingPointComponentBit");

  if (check)
  {
    TypeNode operandType = n[0].getType(check);

    if (!operandType.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "floating-point bit component "
                                         "applied to a non floating-point "
                                         "sort");
    }
    if (!(Theory::isLeafOf(n[0], THEORY_FP)
          || n[0].getKind() == kind::FLOATINGPOINT_TO_FP_REAL))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "floating-point bit component "
                                         "applied to a non leaf / to_fp leaf "
                                         "node");
    }
  }

  return nodeManager->mkBitVectorType(1);
}

TypeNode FloatingPointComponentExponent::computeType(NodeManager* nodeManager,
                                                     TNode n,
                                                     bool check)
{
  TRACE("FloatingPointComponentExponent");

  TypeNode operandType = n[0].getType(check);

  if (check)
  {
    if (!operandType.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "floating-point exponent component "
                                         "applied to a non floating-point "
                                         "sort");
    }
    if (!(Theory::isLeafOf(n[0], THEORY_FP)
          || n[0].getKind() == kind::FLOATINGPOINT_TO_FP_REAL))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "floating-point exponent component "
                                         "applied to a non leaf / to_fp "
                                         "node");
    }
  }

#ifdef CVC5_USE_SYMFPU
  /* Need to create some symfpu objects as the size of bit-vector
   * that is needed for this component is dependent on the encoding
   * used (i.e. whether subnormals are forcibly normalised or not).
   * Here we use types from floatingpoint.h which are the literal
   * back-end but it should't make a difference. */
  FloatingPointSize fps = operandType.getConst<FloatingPointSize>();
  uint32_t bw = FloatingPoint::getUnpackedExponentWidth(fps);
#else
  uint32_t bw = 2;
#endif
  return nodeManager->mkBitVectorType(bw);
}

TypeNode FloatingPointComponentSignificand::computeType(
    NodeManager* nodeManager, TNode n, bool check)
{
  TRACE("FloatingPointComponentSignificand");

  TypeNode operandType = n[0].getType(check);

  if (check)
  {
    if (!operandType.isFloatingPoint())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "floating-point significand "
                                         "component applied to a non "
                                         "floating-point sort");
    }
    if (!(Theory::isLeafOf(n[0], THEORY_FP)
          || n[0].getKind() == kind::FLOATINGPOINT_TO_FP_REAL))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "floating-point significand "
                                         "component applied to a non leaf / "
                                         "to_fp node");
    }
  }

#ifdef CVC5_USE_SYMFPU
  /* As before we need to use some of sympfu. */
  FloatingPointSize fps = operandType.getConst<FloatingPointSize>();
  uint32_t bw = FloatingPoint::getUnpackedSignificandWidth(fps);
#else
  uint32_t bw = 1;
#endif
  return nodeManager->mkBitVectorType(bw);
}

TypeNode RoundingModeBitBlast::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check)
{
  TRACE("RoundingModeBitBlast");

  if (check)
  {
    TypeNode operandType = n[0].getType(check);

    if (!operandType.isRoundingMode())
    {
      throw TypeCheckingExceptionPrivate(
          n, "rounding mode bit-blast applied to a non rounding-mode sort");
    }
    if (!Theory::isLeafOf(n[0], THEORY_FP))
    {
      throw TypeCheckingExceptionPrivate(
          n, "rounding mode bit-blast applied to a non leaf node");
    }
  }

  return nodeManager->mkBitVectorType(CVC5_NUM_ROUNDING_MODES);
}

Cardinality CardinalityComputer::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == kind::FLOATINGPOINT_TYPE);

  FloatingPointSize fps = type.getConst<FloatingPointSize>();

  /*
   * 1                    NaN
   * 2*1                  Infinities
   * 2*1                  Zeros
   * 2*2^(s-1)            Subnormal
   * 2*((2^e)-2)*2^(s-1)  Normal
   *
   *  = 1 + 2*2 + 2*((2^e)-1)*2^(s-1)
   *  =       5 + ((2^e)-1)*2^s
   */

  Integer significandValues = Integer(2).pow(fps.significandWidth());
  Integer exponentValues = Integer(2).pow(fps.exponentWidth());
  exponentValues -= Integer(1);

  return Integer(5) + exponentValues * significandValues;
}

}  // namespace fp
}  // namespace theory
}  // namespace cvc5
