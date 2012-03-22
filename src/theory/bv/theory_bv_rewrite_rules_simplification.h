/*********************                                                        */
/*! \file theory_bv_rewrite_rules_simplification.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

// FIXME: this rules subsume the constant evaluation ones


/**
 * ShlByConst
 *
 * Left Shift by constant amount 
 */
template<>
bool RewriteRule<ShlByConst>::applies(Node node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_SHL &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<>
Node RewriteRule<ShlByConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ShlByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkConst(BitVector(size, Integer(0)));
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));
  
  uint32_t uint32_amount = amount.toUnsignedInt();
  Node left = utils::mkExtract(a, size - 1 - uint32_amount, 0);
  Node right = utils::mkConst(BitVector(uint32_amount, Integer(0))); 
  return utils::mkConcat(left, right); 
}

/**
 * LshrByConst
 *
 * Right Logical Shift by constant amount 
 */

template<>
bool RewriteRule<LshrByConst>::applies(Node node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_LSHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<>
Node RewriteRule<LshrByConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<LshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkConst(BitVector(size, Integer(0)));
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));
  
  uint32_t uint32_amount = amount.toUnsignedInt();
  Node right = utils::mkExtract(a, size - 1, uint32_amount);
  Node left = utils::mkConst(BitVector(uint32_amount, Integer(0))); 
  return utils::mkConcat(left, right); 
}

/**
 * AshrByConst
 *
 * Right Arithmetic Shift by constant amount 
 */

template<>
bool RewriteRule<AshrByConst>::applies(Node node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_ASHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<>
Node RewriteRule<AshrByConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<AshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  Node sign_bit = utils::mkExtract(a, size-1, size-1);
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return n repetitions
    // of the first bit
    return utils::mkConcat(sign_bit, size); 
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));

  uint32_t uint32_amount = amount.toUnsignedInt();
  if (uint32_amount == 0) {
    return a; 
  }
  
  Node left = utils::mkConcat(sign_bit, uint32_amount); 
  Node right = utils::mkExtract(a, size - 1, uint32_amount);
  return utils::mkConcat(left, right); 
}

/**
 * BitwiseIdemp
 *
 * (a bvand a) ==> a
 * (a bvor a)  ==> a
 */

template<>
bool RewriteRule<BitwiseIdemp>::applies(Node node) {
  return ((node.getKind() == kind::BITVECTOR_AND ||
           node.getKind() == kind::BITVECTOR_OR) &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<BitwiseIdemp>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<BitwiseIdemp>(" << node << ")" << std::endl;
  return node[0]; 
}

/**
 * AndZero
 * 
 * (a bvand 0) ==> 0
 */

template<>
bool RewriteRule<AndZero>::applies(Node node) {
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_AND  &&
          (node[0] == utils::mkConst(size, 0) ||
           node[1] == utils::mkConst(size, 0)));
}

template<>
Node RewriteRule<AndZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<AndZero>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/**
 * AndOne
 * 
 * (a bvand 1) ==> a
 */

template<>
bool RewriteRule<AndOne>::applies(Node node) {
  unsigned size = utils::getSize(node);
  Node ones = utils::mkOnes(size); 
  return (node.getKind() == kind::BITVECTOR_AND  &&
          (node[0] == ones ||
           node[1] == ones));
}

template<>
Node RewriteRule<AndOne>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<AndOne>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node);
  
  if (node[0] == utils::mkOnes(size)) {
    return node[1]; 
  } else {
    Assert (node[1] == utils::mkOnes(size)); 
    return node[0]; 
  }
}

/**
 * OrZero
 * 
 * (a bvor 0) ==> a
 */

template<>
bool RewriteRule<OrZero>::applies(Node node) {
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_OR  &&
          (node[0] == utils::mkConst(size, 0) ||
           node[1] == utils::mkConst(size, 0)));
}

template<>
Node RewriteRule<OrZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<OrZero>(" << node << ")" << std::endl;
  
  unsigned size = utils::getSize(node); 
  if (node[0] == utils::mkConst(size, 0)) {
    return node[1]; 
  } else {
    Assert(node[1] == utils::mkConst(size, 0));
    return node[0]; 
  }
}

/**
 * OrOne
 * 
 * (a bvor 1) ==> 1
 */

template<>
bool RewriteRule<OrOne>::applies(Node node) {
  unsigned size = utils::getSize(node);
  Node ones = utils::mkOnes(size); 
  return (node.getKind() == kind::BITVECTOR_OR  &&
          (node[0] == ones ||
           node[1] == ones));
}

template<>
Node RewriteRule<OrOne>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<OrOne>(" << node << ")" << std::endl;
  return utils::mkOnes(utils::getSize(node)); 
}


/**
 * XorDuplicate
 *
 * (a bvxor a) ==> 0
 */

template<>
bool RewriteRule<XorDuplicate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XOR &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<XorDuplicate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorDuplicate>(" << node << ")" << std::endl;
  return utils::mkConst(BitVector(utils::getSize(node), Integer(0))); 
}

/**
 * XorOne
 *
 * (a bvxor 1) ==> ~a
 */

template<>
bool RewriteRule<XorOne>::applies(Node node) {
  Node ones = utils::mkOnes(utils::getSize(node)); 
  return (node.getKind() == kind::BITVECTOR_XOR &&
          (node[0] == ones ||
           node[1] == ones));
}

template<>
Node RewriteRule<XorOne>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorOne>(" << node << ")" << std::endl;
  Node ones = utils::mkOnes(utils::getSize(node)); 
  Node a;
  if (node[0] == ones) {
    a = node[1];
  } else {
    Assert(node[1] == ones);
    a = node[0];
  }

  return utils::mkNode(kind::BITVECTOR_NOT, a);  
}


/**
 * XorZero
 *
 * (a bvxor 0) ==> a
 */

template<>
bool RewriteRule<XorZero>::applies(Node node) {
  Node zero = utils::mkConst(utils::getSize(node), 0); 
  return (node.getKind() == kind::BITVECTOR_XOR &&
          (node[0] == zero ||
           node[1] == zero));
}

template<>
Node RewriteRule<XorZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorZero>(" << node << ")" << std::endl;
  Node zero = utils::mkConst(utils::getSize(node), 0); 
  if (node[0] == zero) {
    return node[1];
  }
  
  Assert(node[1] == zero);
  return node[0];
}


/**
 * BitwiseNotAnd
 *
 * (a bvand (~ a)) ==> 0
 */

template<>
bool RewriteRule<BitwiseNotAnd>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_AND &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<>
Node RewriteRule<BitwiseNotAnd>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<BitwiseNegAnd>(" << node << ")" << std::endl;
  return utils::mkConst(BitVector(utils::getSize(node), Integer(0))); 
}

/**
 * BitwiseNegOr
 *
 * (a bvor (~ a)) ==> 1
 */

template<>
bool RewriteRule<BitwiseNotOr>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_OR &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<>
Node RewriteRule<BitwiseNotOr>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<BitwiseNotOr>(" << node << ")" << std::endl;
  uint32_t size = utils::getSize(node);
  Integer ones = Integer(1).multiplyByPow2(size) - 1; 
  return utils::mkConst(BitVector(size, ones)); 
}

/**
 * XorNot
 *
 * ((~ a) bvxor (~ b)) ==> (a bvxor b)
 */

template<>
bool RewriteRule<XorNot>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XOR &&
          node[0].getKind() == kind::BITVECTOR_NOT &&
          node[1].getKind() == kind::BITVECTOR_NOT); 
}

template<>
Node RewriteRule<XorNot>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorNot>(" << node << ")" << std::endl;
  Node a = node[0][0];
  Node b = node[1][0]; 
  return utils::mkNode(kind::BITVECTOR_XOR, a, b); 
}

/**
 * NotXor
 *
 * ~(a bvxor b) ==> (~ a bvxor b)
 */

template<>
bool RewriteRule<NotXor>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NOT &&
          node[0].getKind() == kind::BITVECTOR_XOR); 
}

template<>
Node RewriteRule<NotXor>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorNot>(" << node << ")" << std::endl;
  Node a = node[0][0];
  Node b = node[0][1];
  Node nota = utils::mkNode(kind::BITVECTOR_NOT, a); 
  return utils::mkNode(kind::BITVECTOR_XOR, nota, b); 
}

/**
 * NotIdemp
 *
 * ~ (~ a) ==> a
 */

template<>
bool RewriteRule<NotIdemp>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NOT &&
          node[0].getKind() == kind::BITVECTOR_NOT); 
}

template<>
Node RewriteRule<NotIdemp>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorIdemp>(" << node << ")" << std::endl;
  return node[0][0];
}



/**
 * LtSelf
 *
 * a < a ==> false
 */

template<>
bool RewriteRule<LtSelf>::applies(Node node) {
  return ((node.getKind() == kind::BITVECTOR_ULT ||
           node.getKind() == kind::BITVECTOR_SLT) &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<LtSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<LtSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}

/**
 * LteSelf
 *
 * a <= a ==> true
 */

template<>
bool RewriteRule<LteSelf>::applies(Node node) {
  return ((node.getKind() == kind::BITVECTOR_ULE ||
           node.getKind() == kind::BITVECTOR_SLE) &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<LteSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<LteSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * UltZero
 *
 * a < 0 ==> false
 */

template<>
bool RewriteRule<UltZero>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<>
Node RewriteRule<UltZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UltZero>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}

/**
 * UltSelf
 *
 * a < a ==> false
 */

template<>
bool RewriteRule<UltSelf>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          node[1] == node[0]); 
}

template<>
Node RewriteRule<UltSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UltSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}


/**
 * UleZero
 *
 * a <= 0 ==> a = 0
 */

template<>
bool RewriteRule<UleZero>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<>
Node RewriteRule<UleZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UleZero>(" << node << ")" << std::endl;
  return utils::mkNode(kind::EQUAL, node[0], node[1]); 
}

/**
 * UleSelf
 *
 * a <= a ==> true
 */

template<>
bool RewriteRule<UleSelf>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == node[0]); 
}

template<>
Node RewriteRule<UleSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UleSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}


/**
 * ZeroUle
 *
 * 0 <= a ==> true
 */

template<>
bool RewriteRule<ZeroUle>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<>
Node RewriteRule<ZeroUle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ZeroUle>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * UleMax
 *
 * a <= 11..1 ==> true
 */

template<>
bool RewriteRule<UleMax>::applies(Node node) {
  if (node.getKind()!= kind::BITVECTOR_ULE) {
    return false; 
  }
  uint32_t size = utils::getSize(node[0]); 
  Integer ones = Integer(1).multiplyByPow2(size) -1; 
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(size, ones)));
}

template<>
Node RewriteRule<UleMax>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UleMax>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * NotUlt
 *
 * ~ ( a < b) ==> b <= a
 */

template<>
bool RewriteRule<NotUlt>::applies(Node node) {
  return (node.getKind() == kind::NOT &&
          node[0].getKind() == kind::BITVECTOR_ULT);
}

template<>
Node RewriteRule<NotUlt>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NotUlt>(" << node << ")" << std::endl;
  Node ult = node[0];
  Node a = ult[0];
  Node b = ult[1]; 
  return utils::mkNode(kind::BITVECTOR_ULE, b, a); 
}

/**
 * NotUle
 *
 * ~ ( a <= b) ==> b < a
 */

template<>
bool RewriteRule<NotUle>::applies(Node node) {
  return (node.getKind() == kind::NOT &&
          node[0].getKind() == kind::BITVECTOR_ULE);
}

template<>
Node RewriteRule<NotUle>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NotUle>(" << node << ")" << std::endl;
  Node ult = node[0];
  Node a = ult[0];
  Node b = ult[1]; 
  return utils::mkNode(kind::BITVECTOR_ULT, b, a); 
}

/**
 * MultOne 
 *
 * (a * 1) ==> a
 */

template<>
bool RewriteRule<MultOne>::applies(Node node) {
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_MULT &&
          (node[0] == utils::mkConst(size, 1) ||
           node[1] == utils::mkConst(size, 1)));
}

template<>
Node RewriteRule<MultOne>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<MultOne>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  if (node[0] == utils::mkConst(size, 1)) {
    return node[1];
  }
  Assert(node[1] == utils::mkConst(size, 1));
  return node[0]; 
}

/**
 * MultZero 
 *
 * (a * 0) ==> 0
 */

template<>
bool RewriteRule<MultZero>::applies(Node node) {
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_MULT &&
          (node[0] == utils::mkConst(size, 0) ||
           node[1] == utils::mkConst(size, 0)));
}

template<>
Node RewriteRule<MultZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<MultZero>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/**
 * MultPow2
 *
 * (a * 2^k) ==> a[n-k-1:0] 0_k
 */

template<>
bool RewriteRule<MultPow2>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_MULT &&
          (utils::isPow2Const(node[0]) ||
           utils::isPow2Const(node[1])));
}

template<>
Node RewriteRule<MultPow2>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<MultPow2>(" << node << ")" << std::endl;
  Node a;
  unsigned power;
  power = utils::isPow2Const(node[0]);

  if (power != 0) {
    a = node[1];
    // isPow2Const returns the power + 1
    --power;
  } else {
    power = utils::isPow2Const(node[1]);
    Assert(power != 0); 
    a = node[0];
    power--; 
  }

  Node extract = utils::mkExtract(a, utils::getSize(node) - power - 1, 0);
  Node zeros = utils::mkConst(power, 0);
  return utils::mkConcat(extract, zeros); 
}

/**
 * PlusZero
 *   
 * (a + 0) ==> a
 */

template<>
bool RewriteRule<PlusZero>::applies(Node node) {
  Node zero = utils::mkConst(utils::getSize(node), 0); 
  return (node.getKind() == kind::BITVECTOR_PLUS &&
          (node[0] == zero ||
           node[1] == zero));
}

template<>
Node RewriteRule<PlusZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<PlusZero>(" << node << ")" << std::endl;
  Node zero = utils::mkConst(utils::getSize(node), 0);
  if (node[0] == zero) {
    return node[1];
  }
  
  return node[0]; 
}

/**
 * NegIdemp
 *
 * -(-a) ==> a 
 */

template<>
bool RewriteRule<NegIdemp>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_NEG);
}

template<>
Node RewriteRule<NegIdemp>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NegIdemp>(" << node << ")" << std::endl;
  return node[0][0]; 
}

/**
 * UdivPow2 
 *
 * (a udiv 2^k) ==> 0_k a[n-1: k]
 */

template<>
bool RewriteRule<UdivPow2>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UDIV &&
          utils::isPow2Const(node[1]));
}

template<>
Node RewriteRule<UdivPow2>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UdivPow2>(" << node << ")" << std::endl;
  Node a = node[0];
  unsigned power = utils::isPow2Const(node[1]) -1;

  Node extract = utils::mkExtract(a, utils::getSize(node) - 1, power);
  Node zeros = utils::mkConst(power, 0);
  
  return utils::mkNode(kind::BITVECTOR_CONCAT, zeros, extract); 
}

/**
 * UdivOne
 *
 * (a udiv 1) ==> a
 */

template<>
bool RewriteRule<UdivOne>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UDIV &&
          node[1] == utils::mkConst(utils::getSize(node), 1));
}

template<>
Node RewriteRule<UdivOne>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UdivOne>(" << node << ")" << std::endl;
  return node[0]; 
}

/**
 * UdivSelf
 *
 * (a udiv a) ==> 1
 */

template<>
bool RewriteRule<UdivSelf>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UDIV &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<UdivSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UdivSelf>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 1); 
}

/**
 * UremPow2
 *
 * (a urem 2^k) ==> 0_(n-k) a[k-1:0]
 */

template<>
bool RewriteRule<UremPow2>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UREM &&
          utils::isPow2Const(node[1]));
}

template<>
Node RewriteRule<UremPow2>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UremPow2>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned power = utils::isPow2Const(node[1]) - 1;
  Node extract = utils::mkExtract(a, power - 1, 0);
  Node zeros = utils::mkConst(utils::getSize(node) - power, 0);
  return utils::mkNode(kind::BITVECTOR_CONCAT, zeros, extract); 
}

/**
 * UremOne
 *
 * (a urem 1) ==> 0
 */

template<>
bool RewriteRule<UremOne>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UREM &&
          node[1] == utils::mkConst(utils::getSize(node), 1));
}

template<>
Node RewriteRule<UremOne>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UremOne>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/**
 * UremSelf 
 *
 * (a urem a) ==> 0
 */

template<>
bool RewriteRule<UremSelf>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UREM &&
          node[0] == node[1]);
}

template<>
Node RewriteRule<UremSelf>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UremSelf>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/**
 * ShiftZero
 *
 * (0_k >> a) ==> 0_k 
 */

template<>
bool RewriteRule<ShiftZero>::applies(Node node) {
  return ((node.getKind() == kind::BITVECTOR_SHL ||
           node.getKind() == kind::BITVECTOR_LSHR ||
           node.getKind() == kind::BITVECTOR_ASHR) &&
          node[0] == utils::mkConst(utils::getSize(node), 0));
}

template<>
Node RewriteRule<ShiftZero>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ShiftZero>(" << node << ")" << std::endl;
  return node[0]; 
}

// /**
//  * 
//  *
//  * 
//  */

// template<>
// bool RewriteRule<>::applies(Node node) {
//   return (node.getKind() == );
// }

// template<>
// Node RewriteRule<>::apply(Node node) {
//   BVDebug("bv-rewrite") << "RewriteRule<>(" << node << ")" << std::endl;
//   return ; 
// }



}
}
}
