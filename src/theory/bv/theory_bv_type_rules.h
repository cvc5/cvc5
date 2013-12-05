/*********************                                                        */
/*! \file theory_bv_type_rules.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Liana Hadarean, Christopher L. Conway, Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#include <algorithm>

#ifndef __CVC4__THEORY__BV__THEORY_BV_TYPE_RULES_H
#define __CVC4__THEORY__BV__THEORY_BV_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace bv {

class BitVectorConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if (check) {
      if (n.getConst<BitVector>().getSize() == 0) {
        throw TypeCheckingExceptionPrivate(n, "constant of size 0");
      }
    }
    return nodeManager->mkBitVectorType(n.getConst<BitVector>().getSize());
  }
};


class BitVectorBitOfTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate) {
    
    if(check) {
      BitVectorBitOf info = n.getOperator().getConst<BitVectorBitOf>();
      TypeNode t = n[0].getType(check);
      
      if (!t.isBitVector()) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
      }
      if (info.bitIndex >= t.getBitVectorSize()) {
        throw TypeCheckingExceptionPrivate(n, "extract index is larger than the bitvector size");
      }
    }
    return nodeManager->booleanType(); 
  }
};


class BitVectorCompRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode lhs = n[0].getType(check);
      TypeNode rhs = n[1].getType(check);
      if (!lhs.isBitVector() || lhs != rhs) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms of the same width");
      }
    }
    return nodeManager->mkBitVectorType(1);
  }
};

class BitVectorFixedWidthTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TNode::iterator it = n.begin();
    TypeNode t = (*it).getType(check);
    if( check ) {
      if (!t.isBitVector()) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
      }
      TNode::iterator it_end = n.end();
      for (++ it; it != it_end; ++ it) {
        if ((*it).getType(check) != t) {
          throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms of the same width");
        }
      }
    }
    return t;
  }
};

class BitVectorPredicateTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode lhsType = n[0].getType(check);
      if (!lhsType.isBitVector()) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
      }
      TypeNode rhsType = n[1].getType(check);
      if (lhsType != rhsType) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms of the same width");
      }
    }
    return nodeManager->booleanType();
  }
};

class BitVectorExtractTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    BitVectorExtract extractInfo = n.getOperator().getConst<BitVectorExtract>();

    // NOTE: We're throwing a type-checking exception here even
    // if check is false, bc if we allow high < low the resulting
    // type will be illegal
    if (extractInfo.high < extractInfo.low) {
      throw TypeCheckingExceptionPrivate(n, "high extract index is smaller than the low extract index");
    }

    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isBitVector()) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
      }
      if (extractInfo.high >= t.getBitVectorSize()) {
        throw TypeCheckingExceptionPrivate(n, "high extract index is bigger than the size of the bit-vector");
      }
    }
    return nodeManager->mkBitVectorType(extractInfo.high - extractInfo.low + 1);
  }
};

class BitVectorExtractOpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::BITVECTOR_EXTRACT_OP);
    return nodeManager->builtinOperatorType();
  }
};

class BitVectorConcatRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    unsigned size = 0;
    TNode::iterator it = n.begin();
    TNode::iterator it_end = n.end();
    for (; it != it_end; ++ it) {
       TypeNode t = (*it).getType(check);
       // NOTE: We're throwing a type-checking exception here even
       // when check is false, bc if we don't check that the arguments
       // are bit-vectors the result type will be inaccurate
       if (!t.isBitVector()) {
         throw TypeCheckingExceptionPrivate(n, "expecting bit-vector terms");
       }
       size += t.getBitVectorSize();
    }
    return nodeManager->mkBitVectorType(size);
  }
};

class BitVectorRepeatTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TypeNode t = n[0].getType(check);
    // NOTE: We're throwing a type-checking exception here even
    // when check is false, bc if the argument isn't a bit-vector
    // the result type will be inaccurate
    if (!t.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    unsigned repeatAmount = n.getOperator().getConst<BitVectorRepeat>();
    return nodeManager->mkBitVectorType(repeatAmount * t.getBitVectorSize());
  }
};

class BitVectorExtendTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    TypeNode t = n[0].getType(check);
    // NOTE: We're throwing a type-checking exception here even
    // when check is false, bc if the argument isn't a bit-vector
    // the result type will be inaccurate
    if (!t.isBitVector()) {
      throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
    }
    unsigned extendAmount = n.getKind() == kind::BITVECTOR_SIGN_EXTEND ?
        (unsigned) n.getOperator().getConst<BitVectorSignExtend>() :
        (unsigned) n.getOperator().getConst<BitVectorZeroExtend>();
    return nodeManager->mkBitVectorType(extendAmount + t.getBitVectorSize());
  }
};

class BitVectorConversionTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if(n.getKind() == kind::BITVECTOR_TO_NAT) {
      if(check && !n[0].getType(check).isBitVector()) {
        throw TypeCheckingExceptionPrivate(n, "expecting bit-vector term");
      }
      return nodeManager->integerType();
    }

    if(n.getKind() == kind::INT_TO_BITVECTOR) {
      size_t bvSize = n.getOperator().getConst<IntToBitVector>();
      if(check && !n[0].getType(check).isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting integer term");
      }
      return nodeManager->mkBitVectorType(bvSize);
    }

    InternalError("bv-conversion typerule invoked for non-bv-conversion kind");
  }
};

class CardinalityComputer {
public:
  inline static Cardinality computeCardinality(TypeNode type) {
    Assert(type.getKind() == kind::BITVECTOR_TYPE);

    unsigned size = type.getConst<BitVectorSize>();
    if(size == 0) {
      return 0;
    }
    Integer i = Integer(2).pow(size);
    return i;
  }
};/* class CardinalityComputer */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_TYPE_RULES_H */
