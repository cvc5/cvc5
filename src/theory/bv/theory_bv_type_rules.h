/*********************                                                        */
/*! \file theory_bv_type_rules.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EXPR_TYPE_THEORY_BV_TYPE_RULES_H_
#define __CVC4__EXPR_TYPE_THEORY_BV_TYPE_RULES_H_

namespace CVC4 {
namespace theory {
namespace bv {

class BitVectorConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    return nodeManager->bitVectorType(n.getConst<BitVector>().getSize());
  }
};

class BitVectorCompRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    TypeNode lhs = n[0].getType();
    TypeNode rhs = n[1].getType();
    if (!lhs.isBitVector() || lhs != rhs) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms of the same width");
    }
    return nodeManager->bitVectorType(1);
  }
};

class BitVectorArithRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    unsigned maxWidth = 0;
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    // TODO: optimize unary neg
    for (; it != it_end; ++ it) {
      TypeNode t = (*it).getType();
      if (!t.isBitVector()) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
      }
      if (maxWidth < t.getBitVectorSize()) maxWidth = t.getBitVectorSize();
    }
    return nodeManager->bitVectorType(maxWidth);
  }
};

class BitVectorFixedWidthTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    TypeNode t = (*it).getType();
    if (!t.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
    }
    for (++ it; it != it_end; ++ it) {
      if ((*it).getType() != t) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms of the same width");
      }
    }
    return t;
  }
};

class BitVectorPredicateTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    TypeNode lhsType = n[0].getType();
    if (!lhsType.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
    }
    TypeNode rhsType = n[1].getType();
    if (lhsType != rhsType) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms of the same width");
    }
    return nodeManager->booleanType();
  }
};

class BitVectorExtractTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    TypeNode t = n[0].getType();
    if (!t.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    BitVectorExtract extractInfo = n.getOperator().getConst<BitVectorExtract>();
    if (extractInfo.high < extractInfo.low) {
      throw TypeCheckingExceptionPrivate(n, "high extract index is smaller than the low extract index");
    }
    if (extractInfo.high >= t.getBitVectorSize()) {
      throw TypeCheckingExceptionPrivate(n, "high extract index is bigger than the size of the bit-vector");
    }
    return nodeManager->bitVectorType(extractInfo.high - extractInfo.low + 1);
  }
};

class BitVectorConcatRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    unsigned size = 0;
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    for (; it != it_end; ++ it) {
       TypeNode t = n[0].getType();
       if (!t.isBitVector()) {
         throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
       }
       size += t.getBitVectorSize();
    }
    return nodeManager->bitVectorType(size);
  }
};

class BitVectorRepeatTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    TypeNode t = n[0].getType();
    if (!t.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    unsigned repeatAmount = n.getOperator().getConst<BitVectorRepeat>();
    return nodeManager->bitVectorType(repeatAmount * t.getBitVectorSize());
  }
};

class BitVectorExtendTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n)
      throw (TypeCheckingExceptionPrivate) {
    TypeNode t = n[0].getType();
    if (!t.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    unsigned extendAmount = n.getKind() == kind::BITVECTOR_SIGN_EXTEND ?
        (unsigned) n.getOperator().getConst<BitVectorSignExtend>() :
        (unsigned) n.getOperator().getConst<BitVectorZeroExtend>();

    return nodeManager->bitVectorType(extendAmount +  t.getBitVectorSize());
  }
};

}
}
}

#endif /* __CVC4__EXPR_TYPE_THEORY_BV_TYPE_RULES_H_ */
