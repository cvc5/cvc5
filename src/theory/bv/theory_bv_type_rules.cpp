/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Leni Aniva
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitvector theory typing rules.
 */

#include "theory/bv/theory_bv_type_rules.h"

#include <algorithm>

#include "expr/type_node.h"
#include "util/bitvector.h"
#include "util/cardinality.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

bool isMaybeBoolean(const TypeNode& tn)
{
  return tn.isBoolean() || tn.isFullyAbstract();
}

/**
 * Return true if tn is maybe a bit-vector type. Write to errOut if it exists
 * and tn is not a maybe bit-vector type.
 */
bool checkMaybeBitVector(const TypeNode& tn, std::ostream* errOut)
{
  if (tn.isMaybeKind(Kind::BITVECTOR_TYPE))
  {
    return true;
  }
  if (errOut)
  {
    (*errOut) << "expecting a bit-vector term";
  }
  return false;
}

/**
 * Ensure that tn is a bit-vector type.
 * Note this is equivalent to tn.leastUpperBound(?BitVec).
 */
TypeNode ensureBv(NodeManager* nm, const TypeNode& tn)
{
  if (tn.getKind() == Kind::ABSTRACT_TYPE
      && tn.getAbstractedKind() == Kind::ABSTRACT_TYPE)
  {
    return nm->mkAbstractType(Kind::BITVECTOR_TYPE);
  }
  return tn;
}

Cardinality CardinalityComputer::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == Kind::BITVECTOR_TYPE);

  uint32_t size = type.getConst<BitVectorSize>();
  if (size == 0)
  {
    return 0;
  }
  return Integer(2).pow(size);
}

TypeNode BitVectorConstantTypeRule::preComputeType(CVC5_UNUSED NodeManager* nm,
                                                   CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorConstantTypeRule::computeType(NodeManager* nodeManager,
                                                TNode n,
                                                bool check,
                                                std::ostream* errOut)
{
  if (check)
  {
    if (n.getConst<BitVector>().getSize() == 0)
    {
      if (errOut)
      {
        (*errOut) << "constant of size 0";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(n.getConst<BitVector>().getSize());
}

TypeNode BitVectorConstantSymbolicTypeRule::preComputeType(
    CVC5_UNUSED NodeManager* nm, CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorConstantSymbolicTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  if (check)
  {
    for (const Node& nc : n)
    {
      const TypeNode& tn = nc.getTypeOrNull();
      if (!tn.isInteger() && !tn.isFullyAbstract())
      {
        (*errOut)
            << "expecting integer argument to symbolic bitvector constant";
        return TypeNode::null();
      }
    }
  }
  if (n[1].isConst())
  {
    const Rational& r = n[1].getConst<Rational>();
    if (r.sgn() == 1 && r.getNumerator().fitsUnsignedInt())
    {
      return nodeManager->mkBitVectorType(r.getNumerator().toUnsignedInt());
    }
  }
  return nodeManager->mkAbstractType(Kind::BITVECTOR_TYPE);
}

TypeNode BitVectorFixedWidthTypeRule::preComputeType(
    CVC5_UNUSED NodeManager* nm, CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorFixedWidthTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  TypeNode t;
  for (const Node& nc : n)
  {
    TypeNode tc = nc.getTypeOrNull();
    if (check)
    {
      if (!checkMaybeBitVector(tc, errOut))
      {
        return TypeNode::null();
      }
    }
    // if first child
    if (t.isNull())
    {
      t = tc;
      continue;
    }
    t = t.leastUpperBound(tc);
    if (t.isNull())
    {
      if (errOut)
      {
        (*errOut) << "expecting comparable bit-vector terms";
      }
      return TypeNode::null();
    }
  }
  // ensure return is bitvector, e.g. if 2 fully abstract children, return
  // ?BitVec.
  return ensureBv(nodeManager, t);
}

TypeNode BitVectorPredicateTypeRule::preComputeType(NodeManager* nm,
                                                    CVC5_UNUSED TNode n)
{
  return nm->booleanType();
}
TypeNode BitVectorPredicateTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  if (check)
  {
    TypeNode lhsType = n[0].getTypeOrNull();
    if (!checkMaybeBitVector(lhsType, errOut))
    {
      return TypeNode::null();
    }
    if (n.getNumChildren() > 1)
    {
      TypeNode rhsType = n[1].getTypeOrNull();
      if (!lhsType.isComparableTo(rhsType))
      {
        if (errOut)
        {
          (*errOut) << "expecting comparable bit-vector terms";
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorRedTypeRule::preComputeType(NodeManager* nm,
                                              CVC5_UNUSED TNode n)
{
  return nm->mkBitVectorType(1);
}
TypeNode BitVectorRedTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  if (check)
  {
    TypeNode type = n[0].getTypeOrNull();
    if (!checkMaybeBitVector(type, errOut))
    {
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(1);
}

TypeNode BitVectorBVPredTypeRule::preComputeType(NodeManager* nm,
                                                 CVC5_UNUSED TNode n)
{
  return nm->mkBitVectorType(1);
}
TypeNode BitVectorBVPredTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  if (check)
  {
    TypeNode lhs = n[0].getTypeOrNull();
    TypeNode rhs = n[1].getTypeOrNull();
    if (!checkMaybeBitVector(lhs, errOut) || !checkMaybeBitVector(rhs, errOut)
        || !lhs.isComparableTo(rhs))
    {
      if (errOut)
      {
        (*errOut) << "expecting comparable bit-vector terms";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(1);
}

TypeNode BitVectorSizeTypeRule::preComputeType(NodeManager* nm,
                                               CVC5_UNUSED TNode n)
{
  return nm->integerType();
}
TypeNode BitVectorSizeTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  TypeNode t = n[0].getTypeOrNull(check);
  if (!checkMaybeBitVector(t, errOut))
  {
    return TypeNode::null();
  }
  return nodeManager->integerType();
}

TypeNode BitVectorConcatTypeRule::preComputeType(CVC5_UNUSED NodeManager* nm,
                                                 CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorConcatTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              CVC5_UNUSED bool check,
                                              std::ostream* errOut)
{
  uint32_t size = 0;
  bool isAbstract = false;
  for (const auto& child : n)
  {
    TypeNode t = child.getTypeOrNull();
    // NOTE: We're throwing a type-checking exception here even
    // when check is false, bc if we don't check that the arguments
    // are bit-vectors the result type will be inaccurate
    if (!checkMaybeBitVector(t, errOut))
    {
      return TypeNode::null();
    }
    if (isAbstract)
    {
      continue;
    }
    else if (t.isAbstract())
    {
      isAbstract = true;
      continue;
    }
    size += t.getBitVectorSize();
  }
  // if any child is abstract, we are abstract
  if (isAbstract)
  {
    return nodeManager->mkAbstractType(Kind::BITVECTOR_TYPE);
  }
  return nodeManager->mkBitVectorType(size);
}

TypeNode BitVectorToBVTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->mkBitVectorType(n.getNumChildren());
}

TypeNode BitVectorToBVTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            CVC5_UNUSED bool check,
                                            std::ostream* errOut)
{
  for (const auto& child : n)
  {
    TypeNode t = child.getTypeOrNull();
    if (!isMaybeBoolean(t))
    {
      if (errOut)
      {
        (*errOut) << "expecting Boolean terms";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->mkBitVectorType(n.getNumChildren());
}

TypeNode BitVectorITETypeRule::preComputeType(CVC5_UNUSED NodeManager* nm,
                                              CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorITETypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getNumChildren() == 3);
  TypeNode thenpart = n[1].getTypeOrNull();
  TypeNode elsepart = n[2].getTypeOrNull();
  // like ite, return is the join of the branches
  TypeNode retType = thenpart.leastUpperBound(elsepart);
  if (check)
  {
    TypeNode cond = n[0].getTypeOrNull();
    if (!nodeManager->mkBitVectorType(1).isComparableTo(cond))
    {
      if (errOut)
      {
        (*errOut) << "expecting condition to be comparable with bit-vector "
                     "term size 1";
      }
      return TypeNode::null();
    }
  }
  if (retType.isNull() && errOut)
  {
    (*errOut) << "expecting then and else parts to have comparable types";
  }
  return retType;
}

TypeNode BitVectorBitTypeRule::preComputeType(NodeManager* nm,
                                              CVC5_UNUSED TNode n)
{
  return nm->booleanType();
}
TypeNode BitVectorBitTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  if (check)
  {
    BitVectorBit info = n.getOperator().getConst<BitVectorBit>();
    TypeNode t = n[0].getTypeOrNull();
    if (!checkMaybeBitVector(t, errOut))
    {
      return TypeNode::null();
    }
    // note this is not checked if the argument has abstract type
    if (t.isBitVector() && info.d_bitIndex >= t.getBitVectorSize())
    {
      if (errOut)
      {
        (*errOut) << "extract index is larger than the bitvector size";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorExtractTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  BitVectorExtract extractInfo = n.getOperator().getConst<BitVectorExtract>();
  return nm->mkBitVectorType(extractInfo.d_high - extractInfo.d_low + 1);
}
TypeNode BitVectorExtractTypeRule::computeType(NodeManager* nodeManager,
                                               TNode n,
                                               bool check,
                                               std::ostream* errOut)
{
  BitVectorExtract extractInfo = n.getOperator().getConst<BitVectorExtract>();

  // NOTE: We're throwing a type-checking exception here even
  // if check is false, bc if we allow high < low the resulting
  // type will be illegal
  if (extractInfo.d_high < extractInfo.d_low)
  {
    if (errOut)
    {
      (*errOut) << "high extract index is smaller than the low extract index";
    }
    return TypeNode::null();
  }

  if (check)
  {
    TypeNode t = n[0].getTypeOrNull();
    if (!checkMaybeBitVector(t, errOut))
    {
      return TypeNode::null();
    }
    // note this is not checked if the argument has abstract type
    if (t.isBitVector() && extractInfo.d_high >= t.getBitVectorSize())
    {
      if (errOut)
      {
        (*errOut)
            << "high extract index is bigger than the size of the bit-vector";
      }
      return TypeNode::null();
    }
  }
  // note that its type is always concrete, even if the argument has abstract
  // type
  return nodeManager->mkBitVectorType(extractInfo.d_high - extractInfo.d_low
                                      + 1);
}

TypeNode BitVectorRepeatTypeRule::preComputeType(CVC5_UNUSED NodeManager* nm,
                                                 CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorRepeatTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              CVC5_UNUSED bool check,
                                              std::ostream* errOut)
{
  TypeNode t = n[0].getTypeOrNull();
  // NOTE: We're throwing a type-checking exception here even
  // when check is false, bc if the argument isn't a bit-vector
  // the result type will be inaccurate
  if (!checkMaybeBitVector(t, errOut))
  {
    return TypeNode::null();
  }
  uint32_t repeatAmount = n.getOperator().getConst<BitVectorRepeat>();
  if (repeatAmount == 0)
  {
    if (errOut)
    {
      (*errOut) << "expecting number of repeats > 0";
    }
    return TypeNode::null();
  }
  // if abstract, we don't take into account the repeat amount, instead we
  // return ?BitVec.
  if (t.isAbstract())
  {
    return ensureBv(nodeManager, t);
  }
  Assert(t.isBitVector());
  return nodeManager->mkBitVectorType(repeatAmount * t.getBitVectorSize());
}

TypeNode BitVectorExtendTypeRule::preComputeType(CVC5_UNUSED NodeManager* nm,
                                                 CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorExtendTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              CVC5_UNUSED bool check,
                                              std::ostream* errOut)
{
  TypeNode t = n[0].getTypeOrNull();
  // NOTE: We're throwing a type-checking exception here even
  // when check is false, bc if the argument isn't a bit-vector
  // the result type will be inaccurate
  if (!checkMaybeBitVector(t, errOut))
  {
    return TypeNode::null();
  }
  if (t.isAbstract())
  {
    return ensureBv(nodeManager, t);
  }
  Assert(t.isBitVector());
  uint32_t extendAmount = n.getKind() == Kind::BITVECTOR_SIGN_EXTEND
                              ? n.getOperator().getConst<BitVectorSignExtend>()
                              : n.getOperator().getConst<BitVectorZeroExtend>();
  return nodeManager->mkBitVectorType(extendAmount + t.getBitVectorSize());
}

TypeNode BitVectorEagerAtomTypeRule::preComputeType(NodeManager* nm,
                                                    CVC5_UNUSED TNode n)
{
  return nm->booleanType();
}
TypeNode BitVectorEagerAtomTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  if (check)
  {
    TypeNode lhsType = n[0].getTypeOrNull();
    // simple check to Boolean
    if (!lhsType.isBoolean())
    {
      if (errOut)
      {
        (*errOut) << "expecting boolean term";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorAckermanizationUdivTypeRule::preComputeType(
    CVC5_UNUSED NodeManager* nm, CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorAckermanizationUdivTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  TypeNode lhsType = n[0].getTypeOrNull();
  if (check)
  {
    if (!checkMaybeBitVector(lhsType, errOut))
    {
      return TypeNode::null();
    }
  }
  return ensureBv(nodeManager, lhsType);
}

TypeNode BitVectorAckermanizationUremTypeRule::preComputeType(
    CVC5_UNUSED NodeManager* nm, CVC5_UNUSED TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorAckermanizationUremTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  TypeNode lhsType = n[0].getTypeOrNull();
  if (check)
  {
    if (!checkMaybeBitVector(lhsType, errOut))
    {
      return TypeNode::null();
    }
  }
  return ensureBv(nodeManager, lhsType);
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
