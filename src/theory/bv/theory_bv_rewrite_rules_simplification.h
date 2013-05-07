/*********************                                                        */
/*! \file theory_bv_rewrite_rules_simplification.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Clark Barrett
 ** Minor contributors (to current version): Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
template<> inline
bool RewriteRule<ShlByConst>::applies(TNode node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_SHL &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<ShlByConst>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ShlByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  
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

template<> inline
bool RewriteRule<LshrByConst>::applies(TNode node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_LSHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<LshrByConst>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<LshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  
  
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

template<> inline
bool RewriteRule<AshrByConst>::applies(TNode node) {
  // if the shift amount is constant
  return (node.getKind() == kind::BITVECTOR_ASHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<AshrByConst>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<AshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  

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

template<> inline
bool RewriteRule<BitwiseIdemp>::applies(TNode node) {
  Unreachable();
  return ((node.getKind() == kind::BITVECTOR_AND ||
           node.getKind() == kind::BITVECTOR_OR) &&
          node.getNumChildren() == 2 &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<BitwiseIdemp>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<BitwiseIdemp>(" << node << ")" << std::endl;
  return node[0]; 
}

/**
 * AndZero
 * 
 * (a bvand 0) ==> 0
 */

template<> inline
bool RewriteRule<AndZero>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_AND  &&
          node.getNumChildren() == 2 &&
          (node[0] == utils::mkConst(size, 0) ||
           node[1] == utils::mkConst(size, 0)));
}

template<> inline
Node RewriteRule<AndZero>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<AndZero>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/**
 * AndOne
 * 
 * (a bvand 1) ==> a
 */

template<> inline
bool RewriteRule<AndOne>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node);
  Node ones = utils::mkOnes(size); 
  return (node.getKind() == kind::BITVECTOR_AND  &&
          node.getNumChildren() == 2 &&
          (node[0] == ones ||
           node[1] == ones));
}

template<> inline
Node RewriteRule<AndOne>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<AndOne>(" << node << ")" << std::endl;
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

template<> inline
bool RewriteRule<OrZero>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node); 
  return (node.getKind() == kind::BITVECTOR_OR  &&
          node.getNumChildren() == 2 &&
          (node[0] == utils::mkConst(size, 0) ||
           node[1] == utils::mkConst(size, 0)));
}

template<> inline
Node RewriteRule<OrZero>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<OrZero>(" << node << ")" << std::endl;
  
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

template<> inline
bool RewriteRule<OrOne>::applies(TNode node) {
  Unreachable();
  unsigned size = utils::getSize(node);
  Node ones = utils::mkOnes(size); 
  return (node.getKind() == kind::BITVECTOR_OR  &&
          node.getNumChildren() == 2 &&
          (node[0] == ones ||
           node[1] == ones));
}

template<> inline
Node RewriteRule<OrOne>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<OrOne>(" << node << ")" << std::endl;
  return utils::mkOnes(utils::getSize(node)); 
}


/**
 * XorDuplicate
 *
 * (a bvxor a) ==> 0
 */

template<> inline
bool RewriteRule<XorDuplicate>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_XOR &&
          node.getNumChildren() == 2 &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<XorDuplicate>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<XorDuplicate>(" << node << ")" << std::endl;
  return utils::mkConst(BitVector(utils::getSize(node), Integer(0))); 
}

/**
 * XorOne
 *
 * (a bvxor 1) ==> ~a
 */

template<> inline
bool RewriteRule<XorOne>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_XOR) {
    return false; 
  }
  Node ones = utils::mkOnes(utils::getSize(node));
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i] == ones) {
      return true; 
    }
  }
  return false; 
}

template<> inline
Node RewriteRule<XorOne>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<XorOne>(" << node << ")" << std::endl;
  Node ones = utils::mkOnes(utils::getSize(node)); 
  std::vector<Node> children;
  bool found_ones = false;
  // XorSimplify should have been called before
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i] == ones) {
      // make sure only ones occurs only once
      found_ones = !found_ones;
    } else {
      children.push_back(node[i]); 
    }
  }

  Node result = utils::mkNode(kind::BITVECTOR_XOR, children);
  if (found_ones) {
    result = utils::mkNode(kind::BITVECTOR_NOT, result);
  }
  return result;
}


/**
 * XorZero
 *
 * (a bvxor 0) ==> a
 */

template<> inline
bool RewriteRule<XorZero>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_XOR) {
    return false; 
  }
  Node zero = utils::mkConst(utils::getSize(node), 0);
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i] == zero) {
      return true; 
    }
  }
  return false; 
}

template<> inline
Node RewriteRule<XorZero>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<XorZero>(" << node << ")" << std::endl;
  std::vector<Node> children;
  Node zero = utils::mkConst(utils::getSize(node), 0);
    
  // XorSimplify should have been called before
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i] != zero) {
      children.push_back(node[i]); 
    }
  }

  return utils::mkNode(kind::BITVECTOR_XOR, children); 
}


/**
 * BitwiseNotAnd
 *
 * (a bvand (~ a)) ==> 0
 */

template<> inline
bool RewriteRule<BitwiseNotAnd>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_AND &&
          node.getNumChildren() == 2 &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<> inline
Node RewriteRule<BitwiseNotAnd>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<BitwiseNegAnd>(" << node << ")" << std::endl;
  return utils::mkConst(BitVector(utils::getSize(node), Integer(0))); 
}

/**
 * BitwiseNegOr
 *
 * (a bvor (~ a)) ==> 1
 */

template<> inline
bool RewriteRule<BitwiseNotOr>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_OR &&
          node.getNumChildren() == 2 &&
          ((node[0].getKind() == kind::BITVECTOR_NOT && node[0][0] == node[1]) ||
           (node[1].getKind() == kind::BITVECTOR_NOT && node[1][0] == node[0]))); 
}

template<> inline
Node RewriteRule<BitwiseNotOr>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<BitwiseNotOr>(" << node << ")" << std::endl;
  uint32_t size = utils::getSize(node);
  Integer ones = Integer(1).multiplyByPow2(size) - 1; 
  return utils::mkConst(BitVector(size, ones)); 
}

/**
 * XorNot
 *
 * ((~ a) bvxor (~ b)) ==> (a bvxor b)
 */

template<> inline
bool RewriteRule<XorNot>::applies(TNode node) {
  Unreachable();
}

template<> inline
Node RewriteRule<XorNot>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<XorNot>(" << node << ")" << std::endl;
  Node a = node[0][0];
  Node b = node[1][0]; 
  return utils::mkNode(kind::BITVECTOR_XOR, a, b); 
}

/**
 * NotXor
 *
 * ~(a bvxor b) ==> (~ a bvxor b)
 */

template<> inline
bool RewriteRule<NotXor>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NOT &&
          node[0].getKind() == kind::BITVECTOR_XOR); 
}

template<> inline
Node RewriteRule<NotXor>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<NotXor>(" << node << ")" << std::endl;
  std::vector<Node> children;
  TNode::iterator child_it = node[0].begin();
  children.push_back(utils::mkNode(kind::BITVECTOR_NOT, *child_it));
  for(++child_it; child_it != node[0].end(); ++child_it) {
    children.push_back(*child_it);
  }
  return utils::mkSortedNode(kind::BITVECTOR_XOR, children);
}

/**
 * NotIdemp
 *
 * ~ (~ a) ==> a
 */

template<> inline
bool RewriteRule<NotIdemp>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NOT &&
          node[0].getKind() == kind::BITVECTOR_NOT); 
}

template<> inline
Node RewriteRule<NotIdemp>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<XorIdemp>(" << node << ")" << std::endl;
  return node[0][0];
}



/**
 * LtSelf
 *
 * a < a ==> false
 */

template<> inline
bool RewriteRule<LtSelf>::applies(TNode node) {
  return ((node.getKind() == kind::BITVECTOR_ULT ||
           node.getKind() == kind::BITVECTOR_SLT) &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<LtSelf>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<LtSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}

/**
 * LteSelf
 *
 * a <= a ==> true
 */

template<> inline
bool RewriteRule<LteSelf>::applies(TNode node) {
  return ((node.getKind() == kind::BITVECTOR_ULE ||
           node.getKind() == kind::BITVECTOR_SLE) &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<LteSelf>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<LteSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * ZeroUlt
 *
 * 0 < a ==> a != 0
 */

template<> inline
bool RewriteRule<ZeroUlt>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          node[0] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<> inline
Node RewriteRule<ZeroUlt>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ZeroUlt>(" << node << ")" << std::endl;
  return utils::mkNode(kind::NOT, utils::mkNode(kind::EQUAL, node[0], node[1])); 
}


/**
 * UltZero
 *
 * a < 0 ==> false
 */

template<> inline
bool RewriteRule<UltZero>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<> inline
Node RewriteRule<UltZero>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UltZero>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}


/**
 * 
 */
template<> inline
bool RewriteRule<UltOne>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(1))));
}

template<> inline
Node RewriteRule<UltOne>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UltOne>(" << node << ")" << std::endl;
  return utils::mkNode(kind::EQUAL, node[0], utils::mkConst(BitVector(utils::getSize(node[0]), 0u))); 
}

/**
 * 
 */
template<> inline
bool RewriteRule<SltZero>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLT &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<> inline
Node RewriteRule<SltZero>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UltZero>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node[0]); 
  Node most_significant_bit = utils::mkExtract(node[0], size - 1, size - 1);
  Node one = utils::mkConst(BitVector(1, 1u));
  
  return utils::mkNode(kind::EQUAL, most_significant_bit, one); 
}


/**
 * UltSelf
 *
 * a < a ==> false
 */

template<> inline
bool RewriteRule<UltSelf>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          node[1] == node[0]); 
}

template<> inline
Node RewriteRule<UltSelf>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UltSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}


/**
 * UleZero
 *
 * a <= 0 ==> a = 0
 */

template<> inline
bool RewriteRule<UleZero>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<> inline
Node RewriteRule<UleZero>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UleZero>(" << node << ")" << std::endl;
  return utils::mkNode(kind::EQUAL, node[0], node[1]); 
}

/**
 * UleSelf
 *
 * a <= a ==> true
 */

template<> inline
bool RewriteRule<UleSelf>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == node[0]); 
}

template<> inline
Node RewriteRule<UleSelf>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UleSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}


/**
 * ZeroUle
 *
 * 0 <= a ==> true
 */

template<> inline
bool RewriteRule<ZeroUle>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[0] == utils::mkConst(BitVector(utils::getSize(node[0]), Integer(0))));
}

template<> inline
Node RewriteRule<ZeroUle>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ZeroUle>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * UleMax
 *
 * a <= 11..1 ==> true
 */

template<> inline
bool RewriteRule<UleMax>::applies(TNode node) {
  if (node.getKind()!= kind::BITVECTOR_ULE) {
    return false; 
  }
  uint32_t size = utils::getSize(node[0]); 
  Integer ones = Integer(1).multiplyByPow2(size) -1; 
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkConst(BitVector(size, ones)));
}

template<> inline
Node RewriteRule<UleMax>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UleMax>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/**
 * NotUlt
 *
 * ~ ( a < b) ==> b <= a
 */

template<> inline
bool RewriteRule<NotUlt>::applies(TNode node) {
  return (node.getKind() == kind::NOT &&
          node[0].getKind() == kind::BITVECTOR_ULT);
}

template<> inline
Node RewriteRule<NotUlt>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<NotUlt>(" << node << ")" << std::endl;
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

template<> inline
bool RewriteRule<NotUle>::applies(TNode node) {
  return (node.getKind() == kind::NOT &&
          node[0].getKind() == kind::BITVECTOR_ULE);
}

template<> inline
Node RewriteRule<NotUle>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<NotUle>(" << node << ")" << std::endl;
  Node ult = node[0];
  Node a = ult[0];
  Node b = ult[1]; 
  return utils::mkNode(kind::BITVECTOR_ULT, b, a); 
}

/**
 * MultPow2
 *
 * (a * 2^k) ==> a[n-k-1:0] 0_k
 */

template<> inline
bool RewriteRule<MultPow2>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_MULT)
    return false;

  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (utils::isPow2Const(node[i])) {
      return true; 
    }
  }
  return false; 
}

template<> inline
Node RewriteRule<MultPow2>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<MultPow2>(" << node << ")" << std::endl;

  std::vector<Node>  children;
  unsigned exponent = 0; 
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    unsigned exp = utils::isPow2Const(node[i]);
    if (exp) {
      exponent += exp - 1;
    }
    else {
      children.push_back(node[i]); 
    }
  }

  Node a = utils::mkNode(kind::BITVECTOR_MULT, children); 

  Node extract = utils::mkExtract(a, utils::getSize(node) - exponent - 1, 0);
  Node zeros = utils::mkConst(exponent, 0);
  return utils::mkConcat(extract, zeros); 
}

/**
 * NegIdemp
 *
 * -(-a) ==> a 
 */

template<> inline
bool RewriteRule<NegIdemp>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_NEG);
}

template<> inline
Node RewriteRule<NegIdemp>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<NegIdemp>(" << node << ")" << std::endl;
  return node[0][0]; 
}

/**
 * UdivPow2 
 *
 * (a udiv 2^k) ==> 0_k a[n-1: k]
 */

template<> inline
bool RewriteRule<UdivPow2>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UDIV_TOTAL &&
          utils::isPow2Const(node[1]));
}

template<> inline
Node RewriteRule<UdivPow2>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UdivPow2>(" << node << ")" << std::endl;
  Node a = node[0];
  unsigned power = utils::isPow2Const(node[1]) -1;
  if (power == 0) {
    return a; 
  }
  Node extract = utils::mkExtract(a, utils::getSize(node) - 1, power);
  Node zeros = utils::mkConst(power, 0);
  
  return utils::mkNode(kind::BITVECTOR_CONCAT, zeros, extract); 
}

/**
 * UdivOne
 *
 * (a udiv 1) ==> a
 */

template<> inline
bool RewriteRule<UdivOne>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UDIV_TOTAL &&
          node[1] == utils::mkConst(utils::getSize(node), 1));
}

template<> inline
Node RewriteRule<UdivOne>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UdivOne>(" << node << ")" << std::endl;
  return node[0]; 
}

/**
 * UdivSelf
 *
 * (a udiv a) ==> 1
 */

template<> inline
bool RewriteRule<UdivSelf>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UDIV_TOTAL &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<UdivSelf>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UdivSelf>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 1); 
}

/**
 * UremPow2
 *
 * (a urem 2^k) ==> 0_(n-k) a[k-1:0]
 */

template<> inline
bool RewriteRule<UremPow2>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UREM_TOTAL &&
          utils::isPow2Const(node[1]));
}

template<> inline
Node RewriteRule<UremPow2>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UremPow2>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned power = utils::isPow2Const(node[1]) - 1;
  if (power == 0) {
    return utils::mkConst(utils::getSize(node), 0);
  }
  Node extract = utils::mkExtract(a, power - 1, 0);
  Node zeros = utils::mkConst(utils::getSize(node) - power, 0);
  return utils::mkNode(kind::BITVECTOR_CONCAT, zeros, extract); 
}

/**
 * UremOne
 *
 * (a urem 1) ==> 0
 */

template<> inline
bool RewriteRule<UremOne>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UREM_TOTAL &&
          node[1] == utils::mkConst(utils::getSize(node), 1));
}

template<> inline
Node RewriteRule<UremOne>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UremOne>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/**
 * UremSelf 
 *
 * (a urem a) ==> 0
 */

template<> inline
bool RewriteRule<UremSelf>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UREM_TOTAL &&
          node[0] == node[1]);
}

template<> inline
Node RewriteRule<UremSelf>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<UremSelf>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/**
 * ShiftZero
 *
 * (0_k >> a) ==> 0_k 
 */

template<> inline
bool RewriteRule<ShiftZero>::applies(TNode node) {
  return ((node.getKind() == kind::BITVECTOR_SHL ||
           node.getKind() == kind::BITVECTOR_LSHR ||
           node.getKind() == kind::BITVECTOR_ASHR) &&
          node[0] == utils::mkConst(utils::getSize(node), 0));
}

template<> inline
Node RewriteRule<ShiftZero>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ShiftZero>(" << node << ")" << std::endl;
  return node[0]; 
}

/**
 * BBPlusNeg
 * 
 * -a1 - a2 - ... - an + ak + ..  ==> - (a1 + a2 + ... + an) + ak
 *
 */

template<> inline
bool RewriteRule<BBPlusNeg>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_PLUS) {
    return false; 
  }

  unsigned neg_count = 0; 
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i].getKind()== kind::BITVECTOR_NEG) {
      ++neg_count; 
    }
  }
  return neg_count > 1;
}

template<> inline
Node RewriteRule<BBPlusNeg>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<BBPlusNeg>(" << node << ")" << std::endl;

  std::vector<Node> children;
  unsigned neg_count = 0; 
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i].getKind() == kind::BITVECTOR_NEG) {
      ++neg_count; 
      children.push_back(utils::mkNode(kind::BITVECTOR_NOT, node[i][0]));
    } else {
      children.push_back(node[i]); 
    }
  }
  Assert(neg_count!= 0); 
  children.push_back(utils::mkConst(utils::getSize(node), neg_count)); 

  return utils::mkNode(kind::BITVECTOR_PLUS, children); 
}

// /**
//  * 
//  *
//  * 
//  */

// template<> inline
// bool RewriteRule<BBFactorOut>::applies(TNode node) {
//   if (node.getKind() != kind::BITVECTOR_PLUS) {
//     return false; 
//   }

//   for (unsigned i = 0; i < node.getNumChildren(); ++i) {
//     if (node[i].getKind() != kind::BITVECTOR_MULT) {
//       return false; 
//     }
//   }
// }

// template<> inline
// Node RewriteRule<BBFactorOut>::apply(TNode node) {
//   Debug("bv-rewrite") << "RewriteRule<BBFactorOut>(" << node << ")" << std::endl;
//   std::hash_set<TNode, TNodeHashFunction> factors;

//   for (unsigned i = 0; i < node.getNumChildren(); ++i) {
//     Assert (node[i].getKind() == kind::BITVECTOR_MULT);
//     for (unsigned j = 0; j < node[i].getNumChildren(); ++j) {
//       factors.insert(node[i][j]); 
//     }
//   }

//   std::vector<TNode> gcd; 
//   std::hash_set<TNode, TNodeHashFunction>::const_iterator it;
//   for (it = factors.begin(); it != factors.end(); ++it) {
//     // for each factor check if it occurs in all children
//     TNode f = *it; 
//     for (unsigned i = 0; i < node.getNumChildren
    
//     }
//   }
//   return ; 
// }


// /**
//  * 
//  *
//  * 
//  */

// template<> inline
// bool RewriteRule<>::applies(TNode node) {
//   return (node.getKind() == );
// }

// template<> inline
// Node RewriteRule<>::apply(TNode node) {
//   Debug("bv-rewrite") << "RewriteRule<>(" << node << ")" << std::endl;
//   return ; 
// }



}
}
}
