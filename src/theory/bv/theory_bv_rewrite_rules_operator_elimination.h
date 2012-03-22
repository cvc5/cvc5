/*********************                                                        */
/*! \file theory_bv_rewrite_rules_core.h
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

template<>
bool RewriteRule<UgtEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UGT);
}

template<>
Node RewriteRule<UgtEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgtEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULT, b, a);
  return result;
}


template<>
bool RewriteRule<UgeEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_UGE);
}

template<>
Node RewriteRule<UgeEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<UgeEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_ULE, b, a);
  return result;
}


template<>
bool RewriteRule<SgtEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SGT);
}

template<>
Node RewriteRule<SgtEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RgewriteRule<UgtEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLT, b, a);
  return result;
}


template<>
bool RewriteRule<SgeEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SGE);
}

template<>
Node RewriteRule<SgeEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SgeEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = utils::mkNode(kind::BITVECTOR_SLE, b, a);
  return result;
}

template <>
bool RewriteRule<SltEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SLT); 
}

template <>
Node RewriteRule<SltEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SltEliminate>(" << node << ")" << std::endl;
  
  unsigned size = utils::getSize(node[0]);
  Node pow_two = utils::mkConst(BitVector(size, Integer(1).multiplyByPow2(size - 1)));
  Node a = utils::mkNode(kind::BITVECTOR_PLUS, node[0], pow_two);
  Node b = utils::mkNode(kind::BITVECTOR_PLUS, node[1], pow_two);
  
  return utils::mkNode(kind::BITVECTOR_ULT, a, b); 
  
}

template <>
bool RewriteRule<SleEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SLE); 
}

template <>
Node RewriteRule<SleEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SleEliminate>(" << node << ")" << std::endl;
  
  unsigned size = utils::getSize(node[0]);
  Node pow_two = utils::mkConst(BitVector(size, Integer(1).multiplyByPow2(size - 1)));
  Node a = utils::mkNode(kind::BITVECTOR_PLUS, node[0], pow_two);
  Node b = utils::mkNode(kind::BITVECTOR_PLUS, node[1], pow_two);
  
  return utils::mkNode(kind::BITVECTOR_ULE, a, b); 
  
}

template <>
bool RewriteRule<CompEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_COMP); 
}

template <>
Node RewriteRule<CompEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<CompEliminate>(" << node << ")" << std::endl;
  Node comp = utils::mkNode(kind::EQUAL, node[0], node[1]);
  Node one = utils::mkConst(1, 1);
  Node zero = utils::mkConst(1, 0); 

  return utils::mkNode(kind::ITE, comp, one, zero);
}

template <>
bool RewriteRule<SubEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SUB); 
}

template <>
Node RewriteRule<SubEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SubEliminate>(" << node << ")" << std::endl;
  Node negb = utils::mkNode(kind::BITVECTOR_NEG, node[1]);
  Node a = node[0];

  return utils::mkNode(kind::BITVECTOR_PLUS, a, negb);
}


template<>
bool RewriteRule<RepeatEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_REPEAT);
}

template<>
Node RewriteRule<RepeatEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<RepeatEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorRepeat>().repeatAmount;
  Assert(amount >= 1);
  if(amount == 1) {
    return a; 
  }
  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
  for(unsigned i = 0; i < amount; ++i) {
    result << node[0]; 
  }
  Node resultNode = result; 
  return resultNode;
}

template<>
bool RewriteRule<RotateLeftEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ROTATE_LEFT);
}

template<>
Node RewriteRule<RotateLeftEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<RotateLeftEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorRotateLeft>().rotateLeftAmount;
  amount = amount % utils::getSize(a); 
  if (amount == 0) {
    return a; 
  }

  Node left   = utils::mkExtract(a, utils::getSize(a)-1 - amount, 0);
  Node right  = utils::mkExtract(a, utils::getSize(a) -1, utils::getSize(a) - amount);
  Node result = utils::mkConcat(left, right);

  return result;
}

template<>
bool RewriteRule<RotateRightEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ROTATE_RIGHT);
}

template<>
Node RewriteRule<RotateRightEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<RotateRightEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorRotateRight>().rotateRightAmount;
  amount = amount % utils::getSize(a); 
  if (amount == 0) {
    return a; 
  }
  
  Node left  = utils::mkExtract(a, amount - 1, 0);
  Node right = utils::mkExtract(a, utils::getSize(a)-1, amount);
  Node result = utils::mkConcat(left, right);

  return result;
}

template<>
bool RewriteRule<NandEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NAND);
}

template<>
Node RewriteRule<NandEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NandEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node andNode = utils::mkNode(kind::BITVECTOR_AND, a, b);
  Node result = utils::mkNode(kind::BITVECTOR_NOT, andNode); 
  return result;
}

template<>
bool RewriteRule<NorEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NOR);
}

template<>
Node RewriteRule<NorEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NorEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node orNode = utils::mkNode(kind::BITVECTOR_OR, a, b);
  Node result = utils::mkNode(kind::BITVECTOR_NOT, orNode); 
  return result;
}

template<>
bool RewriteRule<XnorEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XNOR);
}

template<>
Node RewriteRule<XnorEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XnorEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1]; 
  Node xorNode = utils::mkNode(kind::BITVECTOR_XOR, a, b);
  return utils::mkNode(kind::BITVECTOR_NOT, xorNode); 
}


template<>
bool RewriteRule<SdivEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SDIV);
}

template<>
Node RewriteRule<SdivEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SdivEliminate>(" << node << ")" << std::endl;

  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  
  Node one     = utils::mkConst(1, 1);
  Node a_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), one);
  Node b_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), one); 
  Node abs_a   = utils::mkNode(kind::ITE, a_lt_0, utils::mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b   = utils::mkNode(kind::ITE, b_lt_0, utils::mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_udiv_b   = utils::mkNode(kind::BITVECTOR_UDIV, abs_a, abs_b);
  Node neg_result = utils::mkNode(kind::BITVECTOR_NEG, a_udiv_b);
  
  Node condition = utils::mkNode(kind::XOR, a_lt_0, b_lt_0);
  Node result    = utils::mkNode(kind::ITE, condition, neg_result, a_udiv_b);
  
  return result;
}


template<>
bool RewriteRule<SremEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SREM);
}

template<>
Node RewriteRule<SremEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SremEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  
  Node one     = utils::mkConst(1, 1);
  Node a_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), one);
  Node b_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), one); 
  Node abs_a   = utils::mkNode(kind::ITE, a_lt_0, utils::mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b   = utils::mkNode(kind::ITE, b_lt_0, utils::mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_urem_b   = utils::mkNode(kind::BITVECTOR_UREM, abs_a, abs_b);
  Node neg_result = utils::mkNode(kind::BITVECTOR_NEG, a_urem_b);
  
  Node result    = utils::mkNode(kind::ITE, a_lt_0, neg_result, a_urem_b);

  return result;
}

template<>
bool RewriteRule<SmodEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SMOD);
}

template<>
Node RewriteRule<SmodEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SmodEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  
  Node one     = utils::mkConst(1, 1);
  Node zero    = utils::mkConst(1, 0);
  Node a_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), one);
  Node b_lt_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), one);
  
  Node a_gte_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(a, size-1, size-1), zero);
  Node b_gte_0  = utils::mkNode(kind::EQUAL, utils::mkExtract(b, size-1, size-1), zero); 

  Node abs_a   = utils::mkNode(kind::ITE, a_lt_0, utils::mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b   = utils::mkNode(kind::ITE, b_lt_0, utils::mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_urem_b   = utils::mkNode(kind::BITVECTOR_UREM, abs_a, abs_b);
  Node neg_rem = utils::mkNode(kind::BITVECTOR_NEG, a_urem_b);

  
  Node aneg_bpos = utils::mkNode(kind::AND, a_lt_0, b_gte_0);
  Node apos_bneg = utils::mkNode(kind::AND, a_gte_0, b_lt_0);
  Node aneg_bneg = utils::mkNode(kind::AND, a_lt_0, b_lt_0);
                                 
  Node result = utils::mkNode(kind::ITE, aneg_bpos, utils::mkNode(kind::BITVECTOR_PLUS, neg_rem, b), 
                              utils::mkNode(kind::ITE, apos_bneg, utils::mkNode(kind::BITVECTOR_PLUS, a_urem_b, b),
                                            utils::mkNode(kind::ITE, aneg_bneg, neg_rem,
                                                             a_urem_b)));
  return result;
}


template<>
bool RewriteRule<ZeroExtendEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_ZERO_EXTEND); 
}

template<>
Node RewriteRule<ZeroExtendEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ZeroExtendEliminate>(" << node << ")" << std::endl;

  TNode bv = node[0];
  unsigned amount = node.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount;
  if (amount == 0) {
    return node[0]; 
  }
  Node zero = utils::mkConst(amount, 0);
  Node result = utils::mkConcat(zero, node[0]); 

  return result;
}

template<>
bool RewriteRule<SignExtendEliminate>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_SIGN_EXTEND); 
}

template<>
Node RewriteRule<SignExtendEliminate>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<SignExtendEliminate>(" << node << ")" << std::endl;

  unsigned amount = node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount;
  if(amount == 0) {
    return node[0]; 
  }
  unsigned size = utils::getSize(node[0]); 
  Node sign_bit = utils::mkExtract(node[0], size-1, size-1); 
  Node extension = utils::mkConcat(sign_bit, amount);

  return utils::mkConcat(extension, node[0]);
}


}
}
}
