/*********************                                                        */
/*! \file theory_bv_rewrite_rules_operator_elimination.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "options/bv_options.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

template <>
inline bool RewriteRule<UgtEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_UGT);
}

template <>
inline Node RewriteRule<UgtEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<UgtEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULT, b, a);
  return result;
}

template <>
inline bool RewriteRule<UgeEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_UGE);
}

template <>
inline Node RewriteRule<UgeEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<UgeEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULE, b, a);
  return result;
}

template <>
inline bool RewriteRule<SgtEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SGT);
}

template <>
inline Node RewriteRule<SgtEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SgtEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::currentNM()->mkNode(kind::BITVECTOR_SLT, b, a);
  return result;
}

template <>
inline bool RewriteRule<SgeEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SGE);
}

template <>
inline Node RewriteRule<SgeEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SgeEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::currentNM()->mkNode(kind::BITVECTOR_SLE, b, a);
  return result;
}

template <>
inline bool RewriteRule<SltEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SLT); 
}

template <>
inline Node RewriteRule<SltEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SltEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  unsigned size = utils::getSize(node[0]);
  Integer val = Integer(1).multiplyByPow2(size - 1);
  Node pow_two = utils::mkConst(size, val);
  Node a = nm->mkNode(kind::BITVECTOR_PLUS, node[0], pow_two);
  Node b = nm->mkNode(kind::BITVECTOR_PLUS, node[1], pow_two);

  return nm->mkNode(kind::BITVECTOR_ULT, a, b);
}

template <>
inline bool RewriteRule<SleEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SLE); 
}

template <>
inline Node RewriteRule<SleEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SleEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  Node b_slt_a = nm->mkNode(kind::BITVECTOR_SLT, b, a);
  return nm->mkNode(kind::NOT, b_slt_a);
}

template <>
inline bool RewriteRule<UleEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_ULE); 
}

template <>
inline Node RewriteRule<UleEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<UleEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  Node b_ult_a = nm->mkNode(kind::BITVECTOR_ULT, b, a);
  return nm->mkNode(kind::NOT, b_ult_a);
}

template <>
inline bool RewriteRule<CompEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_COMP); 
}

template <>
inline Node RewriteRule<CompEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<CompEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  Node comp = nm->mkNode(kind::EQUAL, node[0], node[1]);
  Node one = utils::mkConst(1, 1);
  Node zero = utils::mkConst(1, 0);

  return nm->mkNode(kind::ITE, comp, one, zero);
}

template <>
inline bool RewriteRule<SubEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SUB); 
}

template <>
inline Node RewriteRule<SubEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SubEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  Node negb = nm->mkNode(kind::BITVECTOR_NEG, node[1]);
  Node a = node[0];

  return nm->mkNode(kind::BITVECTOR_PLUS, a, negb);
}

template <>
inline bool RewriteRule<RepeatEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_REPEAT);
}

template <>
inline Node RewriteRule<RepeatEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<RepeatEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount =
      node.getOperator().getConst<BitVectorRepeat>().d_repeatAmount;
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

template <>
inline bool RewriteRule<RotateLeftEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_ROTATE_LEFT);
}

template <>
inline Node RewriteRule<RotateLeftEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<RotateLeftEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount =
      node.getOperator().getConst<BitVectorRotateLeft>().d_rotateLeftAmount;
  amount = amount % utils::getSize(a); 
  if (amount == 0) {
    return a; 
  }

  Node left   = utils::mkExtract(a, utils::getSize(a)-1 - amount, 0);
  Node right  = utils::mkExtract(a, utils::getSize(a) -1, utils::getSize(a) - amount);
  Node result = utils::mkConcat(left, right);

  return result;
}

template <>
inline bool RewriteRule<RotateRightEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_ROTATE_RIGHT);
}

template <>
inline Node RewriteRule<RotateRightEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<RotateRightEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount =
      node.getOperator().getConst<BitVectorRotateRight>().d_rotateRightAmount;
  amount = amount % utils::getSize(a); 
  if (amount == 0) {
    return a; 
  }
  
  Node left  = utils::mkExtract(a, amount - 1, 0);
  Node right = utils::mkExtract(a, utils::getSize(a)-1, amount);
  Node result = utils::mkConcat(left, right);

  return result;
}

template <>
inline bool RewriteRule<BVToNatEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_TO_NAT);
}

template <>
inline Node RewriteRule<BVToNatEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<BVToNatEliminate>(" << node << ")" << std::endl;

  //if( node[0].isConst() ){
    //TODO? direct computation instead of term construction+rewriting
  //}
  return utils::eliminateBv2Nat(node);
}

template <>
inline bool RewriteRule<IntToBVEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::INT_TO_BITVECTOR);
}

template <>
inline Node RewriteRule<IntToBVEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<IntToBVEliminate>(" << node << ")" << std::endl;

  //if( node[0].isConst() ){
    //TODO? direct computation instead of term construction+rewriting
  //}
  return utils::eliminateInt2Bv(node);
}

template <>
inline bool RewriteRule<NandEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_NAND &&
          node.getNumChildren() == 2);
}

template <>
inline Node RewriteRule<NandEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<NandEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  Node andNode = nm->mkNode(kind::BITVECTOR_AND, a, b);
  Node result = nm->mkNode(kind::BITVECTOR_NOT, andNode);
  return result;
}

template <>
inline bool RewriteRule<NorEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_NOR && node.getNumChildren() == 2);
}

template <>
inline Node RewriteRule<NorEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<NorEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  Node orNode = nm->mkNode(kind::BITVECTOR_OR, a, b);
  Node result = nm->mkNode(kind::BITVECTOR_NOT, orNode);
  return result;
}

template <>
inline bool RewriteRule<XnorEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_XNOR &&
          node.getNumChildren() == 2);
}

template <>
inline Node RewriteRule<XnorEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<XnorEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  Node xorNode = nm->mkNode(kind::BITVECTOR_XOR, a, b);
  Node result = nm->mkNode(kind::BITVECTOR_NOT, xorNode);
  return result;
}

template <>
inline bool RewriteRule<SdivEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SDIV);
}

template <>
inline Node RewriteRule<SdivEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SdivEliminate>(" << node << ")"
                      << std::endl;

  NodeManager *nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);

  Node one = utils::mkConst(1, 1);
  Node a_lt_0 =
      nm->mkNode(kind::EQUAL, utils::mkExtract(a, size - 1, size - 1), one);
  Node b_lt_0 =
      nm->mkNode(kind::EQUAL, utils::mkExtract(b, size - 1, size - 1), one);
  Node abs_a =
      nm->mkNode(kind::ITE, a_lt_0, nm->mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b =
      nm->mkNode(kind::ITE, b_lt_0, nm->mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_udiv_b =
      nm->mkNode(options::bitvectorDivByZeroConst() ? kind::BITVECTOR_UDIV_TOTAL
                                                    : kind::BITVECTOR_UDIV,
                 abs_a,
                 abs_b);
  Node neg_result = nm->mkNode(kind::BITVECTOR_NEG, a_udiv_b);

  Node condition = nm->mkNode(kind::XOR, a_lt_0, b_lt_0);
  Node result = nm->mkNode(kind::ITE, condition, neg_result, a_udiv_b);

  return result;
}

template <>
inline bool RewriteRule<SremEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SREM);
}

template <>
inline Node RewriteRule<SremEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SremEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);

  Node one = utils::mkConst(1, 1);
  Node a_lt_0 =
      nm->mkNode(kind::EQUAL, utils::mkExtract(a, size - 1, size - 1), one);
  Node b_lt_0 =
      nm->mkNode(kind::EQUAL, utils::mkExtract(b, size - 1, size - 1), one);
  Node abs_a =
      nm->mkNode(kind::ITE, a_lt_0, nm->mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b =
      nm->mkNode(kind::ITE, b_lt_0, nm->mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_urem_b =
      nm->mkNode(options::bitvectorDivByZeroConst() ? kind::BITVECTOR_UREM_TOTAL
                                                    : kind::BITVECTOR_UREM,
                 abs_a,
                 abs_b);
  Node neg_result = nm->mkNode(kind::BITVECTOR_NEG, a_urem_b);

  Node result = nm->mkNode(kind::ITE, a_lt_0, neg_result, a_urem_b);

  return result;
}

template <>
inline bool RewriteRule<SmodEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SMOD);
}

template <>
inline Node RewriteRule<SmodEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SmodEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode s = node[0];
  TNode t = node[1];
  unsigned size = utils::getSize(s);

  // (bvsmod s t) abbreviates
  //     (let ((?msb_s ((_ extract |m-1| |m-1|) s))
  //           (?msb_t ((_ extract |m-1| |m-1|) t)))
  //       (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
  //             (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
  //         (let ((u (bvurem abs_s abs_t)))
  //           (ite (= u (_ bv0 m))
  //                u
  //           (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
  //                u
  //           (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
  //                (bvadd (bvneg u) t)
  //           (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
  //                (bvadd u t)
  //                (bvneg u))))))))

  Node msb_s = utils::mkExtract(s, size - 1, size - 1);
  Node msb_t = utils::mkExtract(t, size - 1, size - 1);

  Node bit1 = utils::mkConst(1, 1);
  Node bit0 = utils::mkConst(1, 0);

  Node abs_s =
      msb_s.eqNode(bit0).iteNode(s, nm->mkNode(kind::BITVECTOR_NEG, s));
  Node abs_t =
      msb_t.eqNode(bit0).iteNode(t, nm->mkNode(kind::BITVECTOR_NEG, t));

  Node u = nm->mkNode(kind::BITVECTOR_UREM, abs_s, abs_t);
  Node neg_u = nm->mkNode(kind::BITVECTOR_NEG, u);

  Node cond0 = u.eqNode(utils::mkConst(size, 0));
  Node cond1 = msb_s.eqNode(bit0).andNode(msb_t.eqNode(bit0));
  Node cond2 = msb_s.eqNode(bit1).andNode(msb_t.eqNode(bit0));
  Node cond3 = msb_s.eqNode(bit0).andNode(msb_t.eqNode(bit1));

  Node result = cond0.iteNode(
      u,
      cond1.iteNode(
          u,
          cond2.iteNode(
              nm->mkNode(kind::BITVECTOR_PLUS, neg_u, t),
              cond3.iteNode(nm->mkNode(kind::BITVECTOR_PLUS, u, t), neg_u))));

  return result;
}

template <>
inline bool RewriteRule<ZeroExtendEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_ZERO_EXTEND); 
}

template <>
inline Node RewriteRule<ZeroExtendEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<ZeroExtendEliminate>(" << node << ")" << std::endl;

  TNode bv = node[0];
  unsigned amount =
      node.getOperator().getConst<BitVectorZeroExtend>().d_zeroExtendAmount;
  if (amount == 0) {
    return node[0]; 
  }
  Node zero = utils::mkConst(amount, 0);
  Node result = utils::mkConcat(zero, node[0]); 

  return result;
}

template <>
inline bool RewriteRule<SignExtendEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SIGN_EXTEND); 
}

template <>
inline Node RewriteRule<SignExtendEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<SignExtendEliminate>(" << node << ")" << std::endl;

  unsigned amount =
      node.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;
  if(amount == 0) {
    return node[0]; 
  }
  unsigned size = utils::getSize(node[0]); 
  Node sign_bit = utils::mkExtract(node[0], size-1, size-1); 
  Node extension = utils::mkConcat(sign_bit, amount);

  return utils::mkConcat(extension, node[0]);
}

template <>
inline bool RewriteRule<RedorEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_REDOR);
}

template <>
inline Node RewriteRule<RedorEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<RedorEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned size = utils::getSize(node[0]); 
  Node result = NodeManager::currentNM()->mkNode(kind::EQUAL, a, utils::mkConst( size, 0 ) );
  return result.negate();
}

template <>
inline bool RewriteRule<RedandEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_REDAND);
}

template <>
inline Node RewriteRule<RedandEliminate>::apply(TNode node)
{
  Debug("bv-rewrite") << "RewriteRule<RedandEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned size = utils::getSize(node[0]); 
  Node result = NodeManager::currentNM()->mkNode(kind::EQUAL, a, utils::mkOnes( size ) );
  return result;
}

}
}
}
