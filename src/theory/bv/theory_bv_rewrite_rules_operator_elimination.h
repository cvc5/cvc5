/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory BV Operator elimination rewrites.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_OPERATOR_ELIMINATION_H
#define CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_OPERATOR_ELIMINATION_H

#include "options/bv_options.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

namespace cvc5::internal {
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
  Trace("bv-rewrite") << "RewriteRule<UgtEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<UgeEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<SgtEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<SgeEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<SltEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  unsigned size = utils::getSize(node[0]);
  Integer val = Integer(1).multiplyByPow2(size - 1);
  Node pow_two = utils::mkConst(size, val);
  Node a = nm->mkNode(kind::BITVECTOR_ADD, node[0], pow_two);
  Node b = nm->mkNode(kind::BITVECTOR_ADD, node[1], pow_two);

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
  Trace("bv-rewrite") << "RewriteRule<SleEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<UleEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<CompEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<SubEliminate>(" << node << ")"
                      << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  Node negb = nm->mkNode(kind::BITVECTOR_NEG, node[1]);
  Node a = node[0];

  return nm->mkNode(kind::BITVECTOR_ADD, a, negb);
}

template <>
inline bool RewriteRule<RepeatEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_REPEAT);
}

template <>
inline Node RewriteRule<RepeatEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<RepeatEliminate>(" << node << ")" << std::endl;
  TNode a = node[0];
  unsigned amount =
      node.getOperator().getConst<BitVectorRepeat>().d_repeatAmount;
  Assert(amount >= 1);
  if(amount == 1) {
    return a; 
  }
  NodeBuilder result(kind::BITVECTOR_CONCAT);
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
  Trace("bv-rewrite") << "RewriteRule<RotateLeftEliminate>(" << node << ")" << std::endl;
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
  Trace("bv-rewrite") << "RewriteRule<RotateRightEliminate>(" << node << ")" << std::endl;
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
inline bool RewriteRule<NandEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_NAND &&
          node.getNumChildren() == 2);
}

template <>
inline Node RewriteRule<NandEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NandEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<NorEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<XnorEliminate>(" << node << ")"
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
  Trace("bv-rewrite") << "RewriteRule<SdivEliminate>(" << node << ")"
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

  Node a_udiv_b = nm->mkNode(kind::BITVECTOR_UDIV, abs_a, abs_b);
  Node neg_result = nm->mkNode(kind::BITVECTOR_NEG, a_udiv_b);

  Node condition = nm->mkNode(kind::XOR, a_lt_0, b_lt_0);
  Node result = nm->mkNode(kind::ITE, condition, neg_result, a_udiv_b);

  return result;
}

/*
 * This rewrite is not meant to be used by the BV rewriter
 * It is specifically designed for the bv-to-int preprocessing pass.
 * Similar to ordinary sdiv elimination.
 * The sign-check is done with bvult instead of bit-extraction.
 */
template <>
inline bool RewriteRule<SdivEliminateFewerBitwiseOps>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SDIV);
}

template <>
inline Node RewriteRule<SdivEliminateFewerBitwiseOps>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SdivEliminateFewerBitwiseOps>(" << node
                      << ")" << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  Node a_lt_0 = nm->mkNode(kind::BITVECTOR_UGE, a, utils::mkMinSigned(size));
  Node b_lt_0 = nm->mkNode(kind::BITVECTOR_UGE, b, utils::mkMinSigned(size));
  Node abs_a =
      nm->mkNode(kind::ITE, a_lt_0, nm->mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b =
      nm->mkNode(kind::ITE, b_lt_0, nm->mkNode(kind::BITVECTOR_NEG, b), b);

  Node a_udiv_b = nm->mkNode(kind::BITVECTOR_UDIV, abs_a, abs_b);
  Node neg_result = nm->mkNode(kind::BITVECTOR_NEG, a_udiv_b);

  Node result = nm->mkNode(kind::ITE, a_lt_0.xorNode(b_lt_0), neg_result, a_udiv_b);

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
  Trace("bv-rewrite") << "RewriteRule<SremEliminate>(" << node << ")"
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

  Node a_urem_b = nm->mkNode(kind::BITVECTOR_UREM, abs_a, abs_b);
  Node neg_result = nm->mkNode(kind::BITVECTOR_NEG, a_urem_b);

  Node result = nm->mkNode(kind::ITE, a_lt_0, neg_result, a_urem_b);

  return result;
}

/*
 * This rewrite is not meant to be used by the BV rewriter
 * It is specifically designed for the bv-to-int preprocessing pass.
 * Similar to ordinary srem elimination.
 * The sign-check is done with bvult instead of bit-extraction.
 */
template <>
inline bool RewriteRule<SremEliminateFewerBitwiseOps>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SREM);
}

template <>
inline Node RewriteRule<SremEliminateFewerBitwiseOps>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SremEliminateFewerBitwiseOps>(" << node
                      << ")" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);
  Node a_lt_0 = nm->mkNode(kind::BITVECTOR_UGE, a, utils::mkMinSigned(size));
  Node b_lt_0 = nm->mkNode(kind::BITVECTOR_UGE, b, utils::mkMinSigned(size));
  Node abs_a =
      nm->mkNode(kind::ITE, a_lt_0, nm->mkNode(kind::BITVECTOR_NEG, a), a);
  Node abs_b =
      nm->mkNode(kind::ITE, b_lt_0, nm->mkNode(kind::BITVECTOR_NEG, b), b);
  Node a_urem_b = nm->mkNode(kind::BITVECTOR_UREM, abs_a, abs_b);
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
  Trace("bv-rewrite") << "RewriteRule<SmodEliminate>(" << node << ")"
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
              nm->mkNode(kind::BITVECTOR_ADD, neg_u, t),
              cond3.iteNode(nm->mkNode(kind::BITVECTOR_ADD, u, t), neg_u))));

  return result;
}

/*
 * This rewrite is not meant to be used by the BV rewriter
 * It is specifically designed for the bv-to-int preprocessing pass.
 * Similar to ordinary smod elimination.
 * The sign-check is done with bvult instead of bit-extraction.
 */
template <>
inline bool RewriteRule<SmodEliminateFewerBitwiseOps>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SMOD);
}

template <>
inline Node RewriteRule<SmodEliminateFewerBitwiseOps>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SmodEliminate>(" << node << ")"
                      << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  TNode s = node[0];
  TNode t = node[1];
  unsigned size = utils::getSize(s);

  /*
   * (bvsmod s t) abbreviates
   *    (let ((?msb_s ((_ extract |m-1| |m-1|) s))
   *          (?msb_t ((_ extract |m-1| |m-1|) t)))
   *      (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
   *            (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
   *        (let ((u (bvurem abs_s abs_t)))
   *          (ite (= u (_ bv0 m))
   *               u
   *          (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
   *               u
   *          (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
   *               (bvadd (bvneg u) t)
   *          (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
   *               (bvadd u t)
   *               (bvneg u))))))))
   */

  Node s_lt_0 = nm->mkNode(kind::BITVECTOR_UGE, s, utils::mkMinSigned(size));
  Node t_lt_0 = nm->mkNode(kind::BITVECTOR_UGE, t, utils::mkMinSigned(size));
  Node abs_s =
      nm->mkNode(kind::ITE, s_lt_0, nm->mkNode(kind::BITVECTOR_NEG, s), s);
  Node abs_t =
      nm->mkNode(kind::ITE, t_lt_0, nm->mkNode(kind::BITVECTOR_NEG, t), t);

  Node u = nm->mkNode(kind::BITVECTOR_UREM, abs_s, abs_t);
  Node neg_u = nm->mkNode(kind::BITVECTOR_NEG, u);

  Node cond0 = u.eqNode(utils::mkConst(size, 0));
  Node cond1 =
      nm->mkNode(kind::NOT, s_lt_0).andNode(nm->mkNode(kind::NOT, t_lt_0));
  Node cond2 = s_lt_0.andNode(nm->mkNode(kind::NOT, t_lt_0));
  Node cond3 = nm->mkNode(kind::NOT, s_lt_0).andNode(t_lt_0);

  Node result = cond0.iteNode(
      u,
      cond1.iteNode(
          u,
          cond2.iteNode(
              nm->mkNode(kind::BITVECTOR_ADD, neg_u, t),
              cond3.iteNode(nm->mkNode(kind::BITVECTOR_ADD, u, t), neg_u))));

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
  Trace("bv-rewrite") << "RewriteRule<ZeroExtendEliminate>(" << node << ")" << std::endl;

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
  Trace("bv-rewrite") << "RewriteRule<SignExtendEliminate>(" << node << ")" << std::endl;

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
  Trace("bv-rewrite") << "RewriteRule<RedorEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  unsigned size = utils::getSize(node[0]);
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(
      kind::BITVECTOR_NOT,
      nm->mkNode(kind::BITVECTOR_COMP, a, utils::mkConst(size, 0)));
}

template <>
inline bool RewriteRule<RedandEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_REDAND);
}

template <>
inline Node RewriteRule<RedandEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<RedandEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  unsigned size = utils::getSize(node[0]);
  Node result = NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_COMP, a, utils::mkOnes(size));
  return result;
}

template <>
inline bool RewriteRule<UaddoEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_UADDO);
}

template <>
inline Node RewriteRule<UaddoEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UaddoEliminate>(" << node << ")"
                      << std::endl;

  NodeManager* nm = NodeManager::currentNM();

  Node bvZero = utils::mkZero(1);
  Node bvOne = utils::mkOne(1);

  Node add = nm->mkNode(kind::BITVECTOR_ADD,
                        utils::mkConcat(bvZero, node[0]),
                        utils::mkConcat(bvZero, node[1]));

  uint32_t size = add.getType().getBitVectorSize();
  return nm->mkNode(
      kind::EQUAL, utils::mkExtract(add, size - 1, size - 1), bvOne);
}

template <>
inline bool RewriteRule<SaddoEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SADDO);
}

template <>
inline Node RewriteRule<SaddoEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SaddoEliminate>(" << node << ")"
                      << std::endl;

  // Overflow occurs if
  //  1) negative + negative = positive
  //  2) positive + positive = negative

  NodeManager* nm = NodeManager::currentNM();
  uint32_t size = node[0].getType().getBitVectorSize();
  Node zero = utils::mkZero(1);
  Node one = utils::mkOne(1);
  Node extOp =
      nm->mkConst<BitVectorExtract>(BitVectorExtract(size - 1, size - 1));
  Node sign0 = nm->mkNode(extOp, node[0]);
  Node sign1 = nm->mkNode(extOp, node[1]);
  Node add = nm->mkNode(kind::BITVECTOR_ADD, node[0], node[1]);
  Node signa = nm->mkNode(extOp, add);

  Node both_neg = nm->mkNode(kind::AND,
                             nm->mkNode(kind::EQUAL, sign0, one),
                             nm->mkNode(kind::EQUAL, sign1, one));
  Node both_pos = nm->mkNode(kind::AND,
                             nm->mkNode(kind::EQUAL, sign0, zero),
                             nm->mkNode(kind::EQUAL, sign1, zero));

  Node result_neg = nm->mkNode(kind::EQUAL, signa, one);
  Node result_pos = nm->mkNode(kind::EQUAL, signa, zero);

  return nm->mkNode(kind::OR,
                    nm->mkNode(kind::AND, both_neg, result_pos),
                    nm->mkNode(kind::AND, both_pos, result_neg));
}

template <>
inline bool RewriteRule<UmuloEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_UMULO);
}

template <>
inline Node RewriteRule<UmuloEliminate>::apply(TNode node)
{
  /* Unsigned multiplication overflow detection.
   * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
   * overflow detection circuits", 2001.
   * http://ieeexplore.ieee.org/document/987767 */

  Trace("bv-rewrite") << "RewriteRule<UmuloEliminate>(" << node << ")"
                      << std::endl;

  uint32_t size = node[0].getType().getBitVectorSize();

  if (size == 1)
  {
    return utils::mkFalse();
  }

  NodeManager* nm = NodeManager::currentNM();
  Node uppc;
  std::vector<Node> tmp;

  uppc = utils::mkExtract(node[0], size - 1, size - 1);
  for (size_t i = 1; i < size; ++i)
  {
    tmp.push_back(
        nm->mkNode(kind::BITVECTOR_AND, utils::mkExtract(node[1], i, i), uppc));
    uppc = nm->mkNode(kind::BITVECTOR_OR,
                      utils::mkExtract(node[0], size - 1 - i, size - 1 - i),
                      uppc);
  }
  Node bvZero = utils::mkZero(1);
  Node zext_t1 = utils::mkConcat(bvZero, node[0]);
  Node zext_t2 = utils::mkConcat(bvZero, node[1]);
  Node mul = nm->mkNode(kind::BITVECTOR_MULT, zext_t1, zext_t2);
  tmp.push_back(utils::mkExtract(mul, size, size));
  return nm->mkNode(
      kind::EQUAL, nm->mkNode(kind::BITVECTOR_OR, tmp), utils::mkOne(1));
}

template <>
inline bool RewriteRule<SmuloEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SMULO);
}

template <>
inline Node RewriteRule<SmuloEliminate>::apply(TNode node)
{
  /* Signed multiplication overflow detection.
   * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
   * overflow detection circuits", 2001.
   * http://ieeexplore.ieee.org/document/987767 */

  Trace("bv-rewrite") << "RewriteRule<SmuloEliminate>(" << node << ")"
                      << std::endl;

  uint32_t size = node[0].getType().getBitVectorSize();
  NodeManager* nm = NodeManager::currentNM();
  Node one = utils::mkOne(1);

  if (size == 1)
  {
    return nm->mkNode(
        kind::EQUAL, nm->mkNode(kind::BITVECTOR_AND, node[0], node[1]), one);
  }

  Node sextOp1 = nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(1));
  Node mul = nm->mkNode(kind::BITVECTOR_MULT,
                        nm->mkNode(sextOp1, node[0]),
                        nm->mkNode(sextOp1, node[1]));

  if (size == 2)
  {
    return nm->mkNode(kind::EQUAL,
                      nm->mkNode(kind::BITVECTOR_XOR,
                                 utils::mkExtract(mul, size, size),
                                 utils::mkExtract(mul, size - 1, size - 1)),
                      one);
  }

  Node sextOpN =
      nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(size - 1));
  Node sign0 = utils::mkExtract(node[0], size - 1, size - 1);
  Node sign1 = utils::mkExtract(node[1], size - 1, size - 1);
  Node xor0 =
      nm->mkNode(kind::BITVECTOR_XOR, node[0], nm->mkNode(sextOpN, sign0));
  Node xor1 =
      nm->mkNode(kind::BITVECTOR_XOR, node[1], nm->mkNode(sextOpN, sign1));

  Node ppc = utils::mkExtract(xor0, size - 2, size - 2);
  Node res = nm->mkNode(kind::BITVECTOR_AND, utils::mkExtract(xor1, 1, 1), ppc);
  for (uint32_t i = 1; i < size - 2; ++i)
  {
    ppc = nm->mkNode(kind::BITVECTOR_OR,
                     ppc,
                     utils::mkExtract(xor0, size - 2 - i, size - 2 - i));
    res = nm->mkNode(
        kind::BITVECTOR_OR,
        res,
        nm->mkNode(
            kind::BITVECTOR_AND, utils::mkExtract(xor1, i + 1, i + 1), ppc));
  }
  return nm->mkNode(
      kind::EQUAL,
      nm->mkNode(kind::BITVECTOR_OR,
                 res,
                 nm->mkNode(kind::BITVECTOR_XOR,
                            utils::mkExtract(mul, size, size),
                            utils::mkExtract(mul, size - 1, size - 1))),
      one);
}

template <>
inline bool RewriteRule<UsuboEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_USUBO);
}

template <>
inline Node RewriteRule<UsuboEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UsuboEliminate>(" << node << ")"
                      << std::endl;

  NodeManager* nm = NodeManager::currentNM();
  Node one = utils::mkOne(1);

  Node zextOp = nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(1));
  Node sub = nm->mkNode(kind::BITVECTOR_SUB,
                        nm->mkNode(zextOp, node[0]),
                        nm->mkNode(zextOp, node[1]));
  uint32_t size = sub.getType().getBitVectorSize();

  Node extOp =
      nm->mkConst<BitVectorExtract>(BitVectorExtract(size - 1, size - 1));
  return nm->mkNode(kind::EQUAL, nm->mkNode(extOp, sub), one);
}

template <>
inline bool RewriteRule<SsuboEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SSUBO);
}

template <>
inline Node RewriteRule<SsuboEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SsuboEliminate>(" << node << ")"
                      << std::endl;

  // Overflow occurs if
  //  1) negative - positive = positive
  //  2) postive - negative = negative

  NodeManager* nm = NodeManager::currentNM();
  uint32_t size = node[0].getType().getBitVectorSize();
  Node one = utils::mkOne(1);
  Node zero = utils::mkZero(1);

  Node extOp =
      nm->mkConst<BitVectorExtract>(BitVectorExtract(size - 1, size - 1));

  Node sign0 = nm->mkNode(extOp, node[0]);
  Node sign1 = nm->mkNode(extOp, node[1]);
  Node sub = nm->mkNode(kind::BITVECTOR_SUB, node[0], node[1]);
  Node signs = nm->mkNode(extOp, sub);

  Node neg_pos = nm->mkNode(kind::AND,
                            nm->mkNode(kind::EQUAL, sign0, one),
                            nm->mkNode(kind::EQUAL, sign1, zero));
  Node pos_neg = nm->mkNode(kind::AND,
                            nm->mkNode(kind::EQUAL, sign0, zero),
                            nm->mkNode(kind::EQUAL, sign1, one));

  Node result_neg = nm->mkNode(kind::EQUAL, signs, one);
  Node result_pos = nm->mkNode(kind::EQUAL, signs, zero);

  return nm->mkNode(kind::OR,
                    nm->mkNode(kind::AND, neg_pos, result_pos),
                    nm->mkNode(kind::AND, pos_neg, result_neg));
}

template <>
inline bool RewriteRule<SdivoEliminate>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_SDIVO);
}

template <>
inline Node RewriteRule<SdivoEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SdivoEliminate>(" << node << ")"
                      << std::endl;
  // Overflow if node[0] = min_signed and node[1] = -1
  NodeManager* nm = NodeManager::currentNM();
  uint64_t size = node[0].getType().getBitVectorSize();
  return nm->mkNode(kind::AND,
                    nm->mkNode(kind::EQUAL, node[0], utils::mkMinSigned(size)),
                    nm->mkNode(kind::EQUAL, node[1], utils::mkOnes(size)));
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif
