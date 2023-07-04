/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Dejan Jovanovic, Andrew Reynolds
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

#include "theory/bv/theory_bv_type_rules.h"

#include <algorithm>

#include "expr/type_node.h"
#include "util/bitvector.h"
#include "util/cardinality.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

Cardinality CardinalityComputer::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == kind::BITVECTOR_TYPE);

  uint32_t size = type.getConst<BitVectorSize>();
  if (size == 0)
  {
    return 0;
  }
  return Integer(2).pow(size);
}

TypeNode BitVectorConstantTypeRule::preComputeType(NodeManager* nm, TNode n)
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
      throw TypeCheckingExceptionPrivate(n, "constant of size 0");
    }
  }
  return nodeManager->mkBitVectorType(n.getConst<BitVector>().getSize());
}

TypeNode BitVectorFixedWidthTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorFixedWidthTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  TNode::iterator it = n.begin();
  TypeNode t = (*it).getType(check);
  if (check)
  {
    if (!t.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
    }
    TNode::iterator it_end = n.end();
    for (++it; it != it_end; ++it)
    {
      if ((*it).getType(check) != t)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting bit-vector terms of the same width");
      }
    }
  }
  return t;
}

TypeNode BitVectorPredicateTypeRule::preComputeType(NodeManager* nm, TNode n)
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
    TypeNode lhsType = n[0].getType(check);
    if (!lhsType.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
    }
    TypeNode rhsType = n[1].getType(check);
    if (lhsType != rhsType)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting bit-vector terms of the same width");
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorRedTypeRule::preComputeType(NodeManager* nm, TNode n)
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
    TypeNode type = n[0].getType(check);
    if (!type.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
  }
  return nodeManager->mkBitVectorType(1);
}

TypeNode BitVectorBVPredTypeRule::preComputeType(NodeManager* nm, TNode n)
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
    TypeNode lhs = n[0].getType(check);
    TypeNode rhs = n[1].getType(check);
    if (!lhs.isBitVector() || lhs != rhs)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting bit-vector terms of the same width");
    }
  }
  return nodeManager->mkBitVectorType(1);
}

TypeNode BitVectorConcatTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorConcatTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  uint32_t size = 0;
  for (const auto& child : n)
  {
    TypeNode t = child.getType(check);
    // NOTE: We're throwing a type-checking exception here even
    // when check is false, bc if we don't check that the arguments
    // are bit-vectors the result type will be inaccurate
    if (!t.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
    }
    size += t.getBitVectorSize();
  }
  return nodeManager->mkBitVectorType(size);
}

TypeNode BitVectorToBVTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->mkBitVectorType(n.getNumChildren());
}

TypeNode BitVectorToBVTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
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

TypeNode BitVectorITETypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorITETypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getNumChildren() == 3);
  TypeNode thenpart = n[1].getType(check);
  if (check)
  {
    TypeNode cond = n[0].getType(check);
    if (cond != nodeManager->mkBitVectorType(1))
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting condition to be bit-vector term size 1");
    }
    TypeNode elsepart = n[2].getType(check);
    if (thenpart != elsepart)
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting then and else parts to have same type");
    }
  }
  return thenpart;
}

TypeNode BitVectorBitOfTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode BitVectorBitOfTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  if (check)
  {
    BitVectorBitOf info = n.getOperator().getConst<BitVectorBitOf>();
    TypeNode t = n[0].getType(check);

    if (!t.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    if (info.d_bitIndex >= t.getBitVectorSize())
    {
      throw TypeCheckingExceptionPrivate(
          n, "extract index is larger than the bitvector size");
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
    throw TypeCheckingExceptionPrivate(
        n, "high extract index is smaller than the low extract index");
  }

  if (check)
  {
    TypeNode t = n[0].getType(check);
    if (!t.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    if (extractInfo.d_high >= t.getBitVectorSize())
    {
      throw TypeCheckingExceptionPrivate(
          n, "high extract index is bigger than the size of the bit-vector");
    }
  }
  return nodeManager->mkBitVectorType(extractInfo.d_high - extractInfo.d_low
                                      + 1);
}

TypeNode BitVectorRepeatTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorRepeatTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  TypeNode t = n[0].getType(check);
  // NOTE: We're throwing a type-checking exception here even
  // when check is false, bc if the argument isn't a bit-vector
  // the result type will be inaccurate
  if (!t.isBitVector())
  {
    throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
  }
  uint32_t repeatAmount = n.getOperator().getConst<BitVectorRepeat>();
  if (repeatAmount == 0)
  {
    throw TypeCheckingExceptionPrivate(n, "expecting number of repeats > 0");
  }
  return nodeManager->mkBitVectorType(repeatAmount * t.getBitVectorSize());
}

TypeNode BitVectorExtendTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorExtendTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  TypeNode t = n[0].getType(check);
  // NOTE: We're throwing a type-checking exception here even
  // when check is false, bc if the argument isn't a bit-vector
  // the result type will be inaccurate
  if (!t.isBitVector())
  {
    throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
  }
  uint32_t extendAmount = n.getKind() == kind::BITVECTOR_SIGN_EXTEND
                              ? n.getOperator().getConst<BitVectorSignExtend>()
                              : n.getOperator().getConst<BitVectorZeroExtend>();
  return nodeManager->mkBitVectorType(extendAmount + t.getBitVectorSize());
}

TypeNode BitVectorEagerAtomTypeRule::preComputeType(NodeManager* nm, TNode n)
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
    TypeNode lhsType = n[0].getType(check);
    if (!lhsType.isBoolean())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting boolean term");
    }
  }
  return nodeManager->booleanType();
}

TypeNode BitVectorAckermanizationUdivTypeRule::preComputeType(NodeManager* nm,
                                                              TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorAckermanizationUdivTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  TypeNode lhsType = n[0].getType(check);
  if (check)
  {
    if (!lhsType.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
  }
  return lhsType;
}

TypeNode BitVectorAckermanizationUremTypeRule::preComputeType(NodeManager* nm,
                                                              TNode n)
{
  return TypeNode::null();
}
TypeNode BitVectorAckermanizationUremTypeRule::computeType(
    NodeManager* nodeManager, TNode n, bool check, std::ostream* errOut)
{
  TypeNode lhsType = n[0].getType(check);
  if (check)
  {
    if (!lhsType.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
  }
  return lhsType;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
