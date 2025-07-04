/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
template <>

inline bool RewriteRule<SizeEliminate>::applies(TNode node)
{
  // ensures argument has concrete bitvector type
  return (node.getKind() == Kind::BITVECTOR_SIZE
          && node[0].getType().isBitVector());
}

template <>
inline Node RewriteRule<SizeEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SizeEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  return node.getNodeManager()->mkConstInt(Rational(utils::getSize(node[0])));
}

template <>
inline bool RewriteRule<UgtEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_UGT);
}

template <>
inline Node RewriteRule<UgtEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UgtEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::mkNode(Kind::BITVECTOR_ULT, b, a);
  return result;
}

template <>
inline bool RewriteRule<UgeEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_UGE);
}

template <>
inline Node RewriteRule<UgeEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UgeEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::mkNode(Kind::BITVECTOR_ULE, b, a);
  return result;
}

template <>
inline bool RewriteRule<SgtEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SGT);
}

template <>
inline Node RewriteRule<SgtEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SgtEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::mkNode(Kind::BITVECTOR_SLT, b, a);
  return result;
}

template <>
inline bool RewriteRule<SgeEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SGE);
}

template <>
inline Node RewriteRule<SgeEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SgeEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node result = NodeManager::mkNode(Kind::BITVECTOR_SLE, b, a);
  return result;
}

template <>
inline bool RewriteRule<SleEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SLE);
}

template <>
inline Node RewriteRule<SleEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SleEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node b_slt_a = NodeManager::mkNode(Kind::BITVECTOR_SLT, b, a);
  return NodeManager::mkNode(Kind::NOT, b_slt_a);
}

template <>
inline bool RewriteRule<UleEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ULE);
}

template <>
inline Node RewriteRule<UleEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UleEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node b_ult_a = NodeManager::mkNode(Kind::BITVECTOR_ULT, b, a);
  return NodeManager::mkNode(Kind::NOT, b_ult_a);
}

template <>
inline bool RewriteRule<SubEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SUB);
}

template <>
inline Node RewriteRule<SubEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SubEliminate>(" << node << ")"
                      << std::endl;
  Node negb = NodeManager::mkNode(Kind::BITVECTOR_NEG, node[1]);
  Node a = node[0];

  return NodeManager::mkNode(Kind::BITVECTOR_ADD, a, negb);
}

template <>
inline bool RewriteRule<RepeatEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_REPEAT);
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
  NodeBuilder result(node.getNodeManager(), Kind::BITVECTOR_CONCAT);
  for(unsigned i = 0; i < amount; ++i) {
    result << node[0]; 
  }
  Node resultNode = result; 
  return resultNode;
}

template <>
inline bool RewriteRule<RotateLeftEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ROTATE_LEFT);
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
  return (node.getKind() == Kind::BITVECTOR_ROTATE_RIGHT);
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
  return (node.getKind() == Kind::BITVECTOR_NAND && node.getNumChildren() == 2);
}

template <>
inline Node RewriteRule<NandEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NandEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node andNode = NodeManager::mkNode(Kind::BITVECTOR_AND, a, b);
  Node result = NodeManager::mkNode(Kind::BITVECTOR_NOT, andNode);
  return result;
}

template <>
inline bool RewriteRule<NorEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_NOR && node.getNumChildren() == 2);
}

template <>
inline Node RewriteRule<NorEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NorEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node orNode = NodeManager::mkNode(Kind::BITVECTOR_OR, a, b);
  Node result = NodeManager::mkNode(Kind::BITVECTOR_NOT, orNode);
  return result;
}

template <>
inline bool RewriteRule<XnorEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_XNOR && node.getNumChildren() == 2);
}

template <>
inline Node RewriteRule<XnorEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<XnorEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  TNode b = node[1];
  Node xorNode = NodeManager::mkNode(Kind::BITVECTOR_XOR, a, b);
  Node result = NodeManager::mkNode(Kind::BITVECTOR_NOT, xorNode);
  return result;
}

template <>
inline bool RewriteRule<SdivEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SDIV);
}

template <>
inline Node RewriteRule<SdivEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SdivEliminate>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);

  Node one = utils::mkConst(nm, 1, 1);
  Node a_lt_0 = NodeManager::mkNode(
      Kind::EQUAL, utils::mkExtract(a, size - 1, size - 1), one);
  Node b_lt_0 = NodeManager::mkNode(
      Kind::EQUAL, utils::mkExtract(b, size - 1, size - 1), one);
  Node abs_a = NodeManager::mkNode(
      Kind::ITE, a_lt_0, NodeManager::mkNode(Kind::BITVECTOR_NEG, a), a);
  Node abs_b = NodeManager::mkNode(
      Kind::ITE, b_lt_0, NodeManager::mkNode(Kind::BITVECTOR_NEG, b), b);

  Node a_udiv_b = NodeManager::mkNode(Kind::BITVECTOR_UDIV, abs_a, abs_b);
  Node neg_result = NodeManager::mkNode(Kind::BITVECTOR_NEG, a_udiv_b);

  Node condition = NodeManager::mkNode(Kind::XOR, a_lt_0, b_lt_0);
  Node result = NodeManager::mkNode(Kind::ITE, condition, neg_result, a_udiv_b);

  return result;
}

template <>
inline bool RewriteRule<SremEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SREM);
}

template <>
inline Node RewriteRule<SremEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SremEliminate>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  TNode a = node[0];
  TNode b = node[1];
  unsigned size = utils::getSize(a);

  Node one = utils::mkConst(nm, 1, 1);
  Node a_lt_0 = NodeManager::mkNode(
      Kind::EQUAL, utils::mkExtract(a, size - 1, size - 1), one);
  Node b_lt_0 = NodeManager::mkNode(
      Kind::EQUAL, utils::mkExtract(b, size - 1, size - 1), one);
  Node abs_a = NodeManager::mkNode(
      Kind::ITE, a_lt_0, NodeManager::mkNode(Kind::BITVECTOR_NEG, a), a);
  Node abs_b = NodeManager::mkNode(
      Kind::ITE, b_lt_0, NodeManager::mkNode(Kind::BITVECTOR_NEG, b), b);

  Node a_urem_b = NodeManager::mkNode(Kind::BITVECTOR_UREM, abs_a, abs_b);
  Node neg_result = NodeManager::mkNode(Kind::BITVECTOR_NEG, a_urem_b);

  Node result = NodeManager::mkNode(Kind::ITE, a_lt_0, neg_result, a_urem_b);

  return result;
}

template <>
inline bool RewriteRule<SmodEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SMOD);
}

template <>
inline Node RewriteRule<SmodEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SmodEliminate>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
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

  Node bit1 = utils::mkConst(nm, 1, 1);
  Node bit0 = utils::mkConst(nm, 1, 0);

  Node abs_s = msb_s.eqNode(bit0).iteNode(
      s, NodeManager::mkNode(Kind::BITVECTOR_NEG, s));
  Node abs_t = msb_t.eqNode(bit0).iteNode(
      t, NodeManager::mkNode(Kind::BITVECTOR_NEG, t));

  Node u = NodeManager::mkNode(Kind::BITVECTOR_UREM, abs_s, abs_t);
  Node neg_u = NodeManager::mkNode(Kind::BITVECTOR_NEG, u);

  Node cond0 = u.eqNode(utils::mkConst(nm, size, 0));
  Node cond1 = msb_s.eqNode(bit0).andNode(msb_t.eqNode(bit0));
  Node cond2 = msb_s.eqNode(bit1).andNode(msb_t.eqNode(bit0));
  Node cond3 = msb_s.eqNode(bit0).andNode(msb_t.eqNode(bit1));

  Node result = cond0.iteNode(
      u,
      cond1.iteNode(
          u,
          cond2.iteNode(
              NodeManager::mkNode(Kind::BITVECTOR_ADD, neg_u, t),
              cond3.iteNode(NodeManager::mkNode(Kind::BITVECTOR_ADD, u, t),
                            neg_u))));

  return result;
}

template <>
inline bool RewriteRule<ZeroExtendEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ZERO_EXTEND);
}

template <>
inline Node RewriteRule<ZeroExtendEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<ZeroExtendEliminate>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  TNode bv = node[0];
  unsigned amount =
      node.getOperator().getConst<BitVectorZeroExtend>().d_zeroExtendAmount;
  if (amount == 0) {
    return node[0]; 
  }
  Node zero = utils::mkConst(nm, amount, 0);
  Node result = utils::mkConcat(zero, node[0]); 

  return result;
}

template <>
inline bool RewriteRule<RedorEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_REDOR);
}

template <>
inline Node RewriteRule<RedorEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<RedorEliminate>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  TNode a = node[0];
  unsigned size = utils::getSize(node[0]);
  return NodeManager::mkNode(
      Kind::BITVECTOR_NOT,
      NodeManager::mkNode(
          Kind::BITVECTOR_COMP, a, utils::mkConst(nm, size, 0)));
}

template <>
inline bool RewriteRule<RedandEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_REDAND);
}

template <>
inline Node RewriteRule<RedandEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<RedandEliminate>(" << node << ")"
                      << std::endl;
  TNode a = node[0];
  unsigned size = utils::getSize(node[0]);
  NodeManager* nm = node.getNodeManager();
  Node result =
      NodeManager::mkNode(Kind::BITVECTOR_COMP, a, utils::mkOnes(nm, size));
  return result;
}

template <>
inline bool RewriteRule<NegoEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_NEGO);
}

template <>
inline Node RewriteRule<NegoEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NegoEliminate>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  return NodeManager::mkNode(
      Kind::EQUAL,
      node[0],
      utils::mkMinSigned(nm, node[0].getType().getBitVectorSize()));
}

template <>
inline bool RewriteRule<UaddoEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_UADDO);
}

template <>
inline Node RewriteRule<UaddoEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UaddoEliminate>(" << node << ")"
                      << std::endl;

  NodeManager* nm = node.getNodeManager();
  Node bvZero = utils::mkZero(nm, 1);
  Node bvOne = utils::mkOne(nm, 1);

  Node add = NodeManager::mkNode(Kind::BITVECTOR_ADD,
                                 utils::mkConcat(bvZero, node[0]),
                                 utils::mkConcat(bvZero, node[1]));

  uint32_t size = add.getType().getBitVectorSize();
  return NodeManager::mkNode(
      Kind::EQUAL, utils::mkExtract(add, size - 1, size - 1), bvOne);
}

template <>
inline bool RewriteRule<SaddoEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SADDO);
}

template <>
inline Node RewriteRule<SaddoEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SaddoEliminate>(" << node << ")"
                      << std::endl;

  // Overflow occurs if
  //  1) negative + negative = positive
  //  2) positive + positive = negative

  NodeManager* nm = node.getNodeManager();
  uint32_t size = node[0].getType().getBitVectorSize();
  Node zero = utils::mkZero(nm, 1);
  Node one = utils::mkOne(nm, 1);
  Node extOp =
      nm->mkConst<BitVectorExtract>(BitVectorExtract(size - 1, size - 1));
  Node sign0 = nm->mkNode(extOp, node[0]);
  Node sign1 = nm->mkNode(extOp, node[1]);
  Node add = NodeManager::mkNode(Kind::BITVECTOR_ADD, node[0], node[1]);
  Node signa = nm->mkNode(extOp, add);

  Node both_neg =
      NodeManager::mkNode(Kind::AND,
                          NodeManager::mkNode(Kind::EQUAL, sign0, one),
                          NodeManager::mkNode(Kind::EQUAL, sign1, one));
  Node both_pos =
      NodeManager::mkNode(Kind::AND,
                          NodeManager::mkNode(Kind::EQUAL, sign0, zero),
                          NodeManager::mkNode(Kind::EQUAL, sign1, zero));

  Node result_neg = NodeManager::mkNode(Kind::EQUAL, signa, one);
  Node result_pos = NodeManager::mkNode(Kind::EQUAL, signa, zero);

  return NodeManager::mkNode(
      Kind::OR,
      NodeManager::mkNode(Kind::AND, both_neg, result_pos),
      NodeManager::mkNode(Kind::AND, both_pos, result_neg));
}

template <>
inline bool RewriteRule<UmuloEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_UMULO);
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

  NodeManager* nm = node.getNodeManager();

  uint32_t size = node[0].getType().getBitVectorSize();

  if (size == 1)
  {
    return utils::mkFalse(nm);
  }

  Node uppc;
  std::vector<Node> tmp;

  uppc = utils::mkExtract(node[0], size - 1, size - 1);
  for (size_t i = 1; i < size; ++i)
  {
    tmp.push_back(
        nm->mkNode(Kind::BITVECTOR_AND, utils::mkExtract(node[1], i, i), uppc));
    uppc = nm->mkNode(Kind::BITVECTOR_OR,
                      utils::mkExtract(node[0], size - 1 - i, size - 1 - i),
                      uppc);
  }
  Node bvZero = utils::mkZero(nm, 1);
  Node zext_t1 = utils::mkConcat(bvZero, node[0]);
  Node zext_t2 = utils::mkConcat(bvZero, node[1]);
  Node mul = nm->mkNode(Kind::BITVECTOR_MULT, zext_t1, zext_t2);
  tmp.push_back(utils::mkExtract(mul, size, size));
  return nm->mkNode(
      Kind::EQUAL, nm->mkNode(Kind::BITVECTOR_OR, tmp), utils::mkOne(nm, 1));
}

template <>
inline bool RewriteRule<SmuloEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SMULO);
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
  NodeManager* nm = node.getNodeManager();
  Node one = utils::mkOne(nm, 1);

  if (size == 1)
  {
    return nm->mkNode(
        Kind::EQUAL, nm->mkNode(Kind::BITVECTOR_AND, node[0], node[1]), one);
  }

  Node sextOp1 = nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(1));
  Node mul = nm->mkNode(Kind::BITVECTOR_MULT,
                        nm->mkNode(sextOp1, node[0]),
                        nm->mkNode(sextOp1, node[1]));

  if (size == 2)
  {
    return nm->mkNode(Kind::EQUAL,
                      nm->mkNode(Kind::BITVECTOR_XOR,
                                 utils::mkExtract(mul, size, size),
                                 utils::mkExtract(mul, size - 1, size - 1)),
                      one);
  }

  Node sextOpN =
      nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(size - 1));
  Node sign0 = utils::mkExtract(node[0], size - 1, size - 1);
  Node sign1 = utils::mkExtract(node[1], size - 1, size - 1);
  Node xor0 =
      nm->mkNode(Kind::BITVECTOR_XOR, node[0], nm->mkNode(sextOpN, sign0));
  Node xor1 =
      nm->mkNode(Kind::BITVECTOR_XOR, node[1], nm->mkNode(sextOpN, sign1));

  Node ppc = utils::mkExtract(xor0, size - 2, size - 2);
  Node res = nm->mkNode(Kind::BITVECTOR_AND, utils::mkExtract(xor1, 1, 1), ppc);
  for (uint32_t i = 1; i < size - 2; ++i)
  {
    ppc = nm->mkNode(Kind::BITVECTOR_OR,
                     ppc,
                     utils::mkExtract(xor0, size - 2 - i, size - 2 - i));
    res = nm->mkNode(
        Kind::BITVECTOR_OR,
        res,
        nm->mkNode(
            Kind::BITVECTOR_AND, utils::mkExtract(xor1, i + 1, i + 1), ppc));
  }
  return nm->mkNode(
      Kind::EQUAL,
      nm->mkNode(Kind::BITVECTOR_OR,
                 res,
                 nm->mkNode(Kind::BITVECTOR_XOR,
                            utils::mkExtract(mul, size, size),
                            utils::mkExtract(mul, size - 1, size - 1))),
      one);
}

template <>
inline bool RewriteRule<UsuboEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_USUBO);
}

template <>
inline Node RewriteRule<UsuboEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UsuboEliminate>(" << node << ")"
                      << std::endl;

  NodeManager* nm = node.getNodeManager();
  Node one = utils::mkOne(nm, 1);

  Node zextOp = nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(1));
  Node sub = nm->mkNode(Kind::BITVECTOR_SUB,
                        nm->mkNode(zextOp, node[0]),
                        nm->mkNode(zextOp, node[1]));
  uint32_t size = sub.getType().getBitVectorSize();

  Node extOp =
      nm->mkConst<BitVectorExtract>(BitVectorExtract(size - 1, size - 1));
  return nm->mkNode(Kind::EQUAL, nm->mkNode(extOp, sub), one);
}

template <>
inline bool RewriteRule<SsuboEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SSUBO);
}

template <>
inline Node RewriteRule<SsuboEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SsuboEliminate>(" << node << ")"
                      << std::endl;

  // Overflow occurs if
  //  1) negative - positive = positive
  //  2) postive - negative = negative

  NodeManager* nm = node.getNodeManager();
  uint32_t size = node[0].getType().getBitVectorSize();
  Node one = utils::mkOne(nm, 1);
  Node zero = utils::mkZero(nm, 1);

  Node extOp =
      nm->mkConst<BitVectorExtract>(BitVectorExtract(size - 1, size - 1));

  Node sign0 = nm->mkNode(extOp, node[0]);
  Node sign1 = nm->mkNode(extOp, node[1]);
  Node sub = nm->mkNode(Kind::BITVECTOR_SUB, node[0], node[1]);
  Node signs = nm->mkNode(extOp, sub);

  Node neg_pos = nm->mkNode(Kind::AND,
                            nm->mkNode(Kind::EQUAL, sign0, one),
                            nm->mkNode(Kind::EQUAL, sign1, zero));
  Node pos_neg = nm->mkNode(Kind::AND,
                            nm->mkNode(Kind::EQUAL, sign0, zero),
                            nm->mkNode(Kind::EQUAL, sign1, one));

  Node result_neg = nm->mkNode(Kind::EQUAL, signs, one);
  Node result_pos = nm->mkNode(Kind::EQUAL, signs, zero);

  return nm->mkNode(Kind::OR,
                    nm->mkNode(Kind::AND, neg_pos, result_pos),
                    nm->mkNode(Kind::AND, pos_neg, result_neg));
}

template <>
inline bool RewriteRule<SdivoEliminate>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_SDIVO);
}

template <>
inline Node RewriteRule<SdivoEliminate>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SdivoEliminate>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  // Overflow if node[0] = min_signed and node[1] = -1
  uint64_t size = node[0].getType().getBitVectorSize();
  return NodeManager::mkNode(
      Kind::AND,
      NodeManager::mkNode(Kind::EQUAL, node[0], utils::mkMinSigned(nm, size)),
      NodeManager::mkNode(Kind::EQUAL, node[1], utils::mkOnes(nm, size)));
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif
