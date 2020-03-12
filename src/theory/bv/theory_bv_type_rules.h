/*********************                                                        */
/*! \file theory_bv_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory typing rules
 **
 ** Bitvector theory typing rules.
 **/

#include "cvc4_private.h"

#include <algorithm>

#ifndef CVC4__THEORY__BV__THEORY_BV_TYPE_RULES_H
#define CVC4__THEORY__BV__THEORY_BV_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

class CardinalityComputer
{
 public:
  inline static Cardinality computeCardinality(TypeNode type)
  {
    Assert(type.getKind() == kind::BITVECTOR_TYPE);

    unsigned size = type.getConst<BitVectorSize>();
    if (size == 0)
    {
      return 0;
    }
    Integer i = Integer(2).pow(size);
    return i;
  }
}; /* class CardinalityComputer */

/* -------------------------------------------------------------------------- */

class BitVectorConstantTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorConstantTypeRule */

/* -------------------------------------------------------------------------- */

class BitVectorFixedWidthTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorFixedWidthTypeRule */

/* -------------------------------------------------------------------------- */

class BitVectorPredicateTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorPredicateTypeRule */

class BitVectorUnaryPredicateTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (check)
    {
      TypeNode type = n[0].getType(check);
      if (!type.isBitVector())
      {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
      }
    }
    return nodeManager->booleanType();
  }
}; /* class BitVectorUnaryPredicateTypeRule */

class BitVectorBVPredTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorBVPredTypeRule */

/* -------------------------------------------------------------------------- */
/* non-parameterized operator kinds                                           */
/* -------------------------------------------------------------------------- */

class BitVectorConcatTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    unsigned size = 0;
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    for (; it != it_end; ++it)
    {
      TypeNode t = (*it).getType(check);
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
}; /* class BitVectorConcatTypeRule */

class BitVectorITETypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorITETypeRule */

/* -------------------------------------------------------------------------- */
/* parameterized operator kinds                                               */
/* -------------------------------------------------------------------------- */

class BitVectorBitOfTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorBitOfTypeRule */

class BitVectorExtractTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorExtractTypeRule */

class BitVectorRepeatTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode t = n[0].getType(check);
    // NOTE: We're throwing a type-checking exception here even
    // when check is false, bc if the argument isn't a bit-vector
    // the result type will be inaccurate
    if (!t.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    unsigned repeatAmount = n.getOperator().getConst<BitVectorRepeat>();
    return nodeManager->mkBitVectorType(repeatAmount * t.getBitVectorSize());
  }
}; /* class BitVectorRepeatTypeRule */

class BitVectorExtendTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode t = n[0].getType(check);
    // NOTE: We're throwing a type-checking exception here even
    // when check is false, bc if the argument isn't a bit-vector
    // the result type will be inaccurate
    if (!t.isBitVector())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    unsigned extendAmount =
        n.getKind() == kind::BITVECTOR_SIGN_EXTEND
            ? (unsigned)n.getOperator().getConst<BitVectorSignExtend>()
            : (unsigned)n.getOperator().getConst<BitVectorZeroExtend>();
    return nodeManager->mkBitVectorType(extendAmount + t.getBitVectorSize());
  }
}; /* class BitVectorExtendTypeRule */

class IntToBitVectorOpTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (n.getKind() == kind::INT_TO_BITVECTOR_OP)
    {
      size_t bvSize = n.getConst<IntToBitVector>();
      return nodeManager->mkFunctionType(nodeManager->integerType(),
                                         nodeManager->mkBitVectorType(bvSize));
    }

    InternalError()
        << "bv-conversion typerule invoked for non-bv-conversion kind";
  }
}; /* class IntToBitVectorOpTypeRule */

class BitVectorConversionTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (n.getKind() == kind::BITVECTOR_TO_NAT)
    {
      if (check && !n[0].getType(check).isBitVector())
      {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
      }
      return nodeManager->integerType();
    }

    if (n.getKind() == kind::INT_TO_BITVECTOR)
    {
      size_t bvSize = n.getOperator().getConst<IntToBitVector>();
      if (check && !n[0].getType(check).isInteger())
      {
        throw TypeCheckingExceptionPrivate(n, "expecting integer term");
      }
      return nodeManager->mkBitVectorType(bvSize);
    }

    InternalError()
        << "bv-conversion typerule invoked for non-bv-conversion kind";
  }
}; /* class BitVectorConversionTypeRule */

/* -------------------------------------------------------------------------- */
/* internal                                                                   */
/* -------------------------------------------------------------------------- */

class BitVectorEagerAtomTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorEagerAtomTypeRule */

class BitVectorAckermanizationUdivTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorAckermanizationUdivTypeRule */

class BitVectorAckermanizationUremTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
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
}; /* class BitVectorAckermanizationUremTypeRule */

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BV__THEORY_BV_TYPE_RULES_H */
