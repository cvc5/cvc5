/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simplification rewrite rules of the BV theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_SIMPLIFICATION_H
#define CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_SIMPLIFICATION_H

#include "options/bv_options.h"
#include "theory/arith/arith_utilities.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/* -------------------------------------------------------------------------- */

/**
 * BitConst
 */
template <>
inline bool RewriteRule<BitConst>::applies(TNode node)
{
  return node.getKind() == Kind::BITVECTOR_BIT && node[0].isConst();
}

template <>
inline Node RewriteRule<BitConst>::apply(TNode node)
{
  size_t pos = node.getOperator().getConst<BitVectorBit>().d_bitIndex;
  NodeManager* nm = node.getNodeManager();
  return utils::getBit(node[0], pos) ? utils::mkTrue(nm) : utils::mkFalse(nm);
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteConstCond
 *
 * BITVECTOR_ITE with constant condition
 */
template <>
inline bool RewriteRule<BvIteConstCond>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ITE && node[0].isConst());
}

template <>
inline Node RewriteRule<BvIteConstCond>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteConstCond>(" << node << ")"
                      << std::endl;
  return utils::isZero(node[0]) ? node[2] : node[1];
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteEqualChildren
 *
 * BITVECTOR_ITE with term_then = term_else
 */
template <>
inline bool RewriteRule<BvIteEqualChildren>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ITE && node[1] == node[2]);
}

template <>
inline Node RewriteRule<BvIteEqualChildren>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteEqualChildren>(" << node << ")"
                      << std::endl;
  return node[1];
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteConstChildren
 *
 * BITVECTOR_ITE with constant children of size one
 */
template <>
inline bool RewriteRule<BvIteConstChildren>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ITE && utils::getSize(node[1]) == 1
          && node[1].isConst() && node[2].isConst());
}

template <>
inline Node RewriteRule<BvIteConstChildren>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteConstChildren>(" << node << ")"
                      << std::endl;
  if (utils::isOne(node[1]) && utils::isZero(node[2]))
  {
    return node[0];
  }
  Assert(utils::isZero(node[1]) && utils::isOne(node[2]));
  return NodeManager::mkNode(Kind::BITVECTOR_NOT, node[0]);
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteEqualCond
 *
 * Nested BITVECTOR_ITE with cond_outer == cond_inner
 *
 * c0 ? (c0 ? t0 : e0) : e1              ->  c0 ? t0 : e1
 * c0 ? t0             : (c0 ? t1 : e1)  ->  c0 ? t0 : e1
 * c0 ? (c0 ? t0 : e0) : (c0 ? t1 : e1)  ->  c0 ? t0 : e1
 */
template <>
inline bool RewriteRule<BvIteEqualCond>::applies(TNode node)
{
  return (
      node.getKind() == Kind::BITVECTOR_ITE
      && ((node[1].getKind() == Kind::BITVECTOR_ITE && node[0] == node[1][0])
          || (node[2].getKind() == Kind::BITVECTOR_ITE
              && node[0] == node[2][0])));
}

template <>
inline Node RewriteRule<BvIteEqualCond>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteEqualCond>(" << node << ")"
                      << std::endl;
  Node t0 = node[1].getKind() == Kind::BITVECTOR_ITE && node[0] == node[1][0]
                ? node[1][1]
                : node[1];
  Node e1 = node[2].getKind() == Kind::BITVECTOR_ITE && node[0] == node[2][0]
                ? node[2][2]
                : node[2];
  return NodeManager::mkNode(Kind::BITVECTOR_ITE, node[0], t0, e1);
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeThenIf
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? (c1 ? t1 : e1) : t1  ->  c0 AND NOT(c1) ? e1 : t1
 */
template <>
inline bool RewriteRule<BvIteMergeThenIf>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ITE
          && node[1].getKind() == Kind::BITVECTOR_ITE && node[1][1] == node[2]);
}

template <>
inline Node RewriteRule<BvIteMergeThenIf>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeThenIf>(" << node << ")"
                      << std::endl;
  Assert(node[1].getKind() == Kind::BITVECTOR_ITE);
  Node cond =
      NodeManager::mkNode(Kind::BITVECTOR_AND,
                          node[0],
                          NodeManager::mkNode(Kind::BITVECTOR_NOT, node[1][0]));
  return NodeManager::mkNode(Kind::BITVECTOR_ITE, cond, node[1][2], node[2]);
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeElseIf
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? (c1 ? t1 : e1) : e1  ->  c0 AND c1 ? t1 : e1
 */
template <>
inline bool RewriteRule<BvIteMergeElseIf>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ITE
          && node[1].getKind() == Kind::BITVECTOR_ITE && node[1][2] == node[2]);
}

template <>
inline Node RewriteRule<BvIteMergeElseIf>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeElseIf>(" << node << ")"
                      << std::endl;
  Assert(node[1].getKind() == Kind::BITVECTOR_ITE);
  Node cond = NodeManager::mkNode(Kind::BITVECTOR_AND, node[0], node[1][0]);
  return NodeManager::mkNode(Kind::BITVECTOR_ITE, cond, node[1][1], node[2]);
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeThenElse
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? t0 : (c1 ? t0 : e1)  ->  NOT(c0) AND NOT(c1) ? e1 : t0
 */
template <>
inline bool RewriteRule<BvIteMergeThenElse>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ITE
          && node[2].getKind() == Kind::BITVECTOR_ITE && node[1] == node[2][1]);
}

template <>
inline Node RewriteRule<BvIteMergeThenElse>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeThenElse>(" << node << ")"
                      << std::endl;
  Assert(node[2].getKind() == Kind::BITVECTOR_ITE);
  Node cond =
      NodeManager::mkNode(Kind::BITVECTOR_AND,
                          NodeManager::mkNode(Kind::BITVECTOR_NOT, node[0]),
                          NodeManager::mkNode(Kind::BITVECTOR_NOT, node[2][0]));
  return NodeManager::mkNode(Kind::BITVECTOR_ITE, cond, node[2][2], node[1]);
}

/* -------------------------------------------------------------------------- */

/**
 * BvIteMergeElseElse
 *
 * Nested BITVECTOR_ITE of the form
 *   c0 ? t0 : (c1 ? t1 : t0)  ->  NOT(c0) AND c1 ? t1 : t0
 */
template <>
inline bool RewriteRule<BvIteMergeElseElse>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ITE
          && node[2].getKind() == Kind::BITVECTOR_ITE && node[1] == node[2][2]);
}

template <>
inline Node RewriteRule<BvIteMergeElseElse>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeElseElse>(" << node << ")"
                      << std::endl;
  Assert(node[2].getKind() == Kind::BITVECTOR_ITE);
  Node cond =
      NodeManager::mkNode(Kind::BITVECTOR_AND,
                          NodeManager::mkNode(Kind::BITVECTOR_NOT, node[0]),
                          node[2][0]);
  return NodeManager::mkNode(Kind::BITVECTOR_ITE, cond, node[2][1], node[1]);
}

/* -------------------------------------------------------------------------- */

/**
 * BvComp
 *
 * BITVECTOR_COMP of children of size 1 with one constant child
 */
template <>
inline bool RewriteRule<BvComp>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_COMP && utils::getSize(node[0]) == 1
          && (node[0].isConst() || node[1].isConst()));
}

template <>
inline Node RewriteRule<BvComp>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvComp>(" << node << ")" << std::endl;
  if (node[0].isConst())
  {
    return utils::isZero(node[0])
               ? NodeManager::mkNode(Kind::BITVECTOR_NOT, node[1])
               : Node(node[1]);
  }
  return utils::isZero(node[1])
             ? NodeManager::mkNode(Kind::BITVECTOR_NOT, node[0])
             : Node(node[0]);
}

/* -------------------------------------------------------------------------- */

/**
 * ShlByConst
 *
 * Left Shift by constant amount 
 */
template<> inline
bool RewriteRule<ShlByConst>::applies(TNode node) {
  // if the shift amount is constant
  return (node.getKind() == Kind::BITVECTOR_SHL
          && node[1].getKind() == Kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<ShlByConst>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ShlByConst>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkZero(nm, size);
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));

  uint32_t uint32_amount = amount.toUnsignedInt();

  Node left = utils::mkExtract(a, size - 1 - uint32_amount, 0);
  Node right = utils::mkZero(nm, uint32_amount);
  return utils::mkConcat(left, right); 
}

/* -------------------------------------------------------------------------- */

/**
 * LshrByConst
 *
 * Right Logical Shift by constant amount 
 */

template<> inline
bool RewriteRule<LshrByConst>::applies(TNode node) {
  // if the shift amount is constant
  return (node.getKind() == Kind::BITVECTOR_LSHR
          && node[1].getKind() == Kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<LshrByConst>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<LshrByConst>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkZero(nm, size);
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));

  uint32_t uint32_amount = amount.toUnsignedInt();
  Node right = utils::mkExtract(a, size - 1, uint32_amount);
  Node left = utils::mkZero(nm, uint32_amount);
  return utils::mkConcat(left, right); 
}

/* -------------------------------------------------------------------------- */

/**
 * AshrByConst
 *
 * Right Arithmetic Shift by constant amount 
 */

template<> inline
bool RewriteRule<AshrByConst>::applies(TNode node) {
  // if the shift amount is constant
  return (node.getKind() == Kind::BITVECTOR_ASHR
          && node[1].getKind() == Kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<AshrByConst>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<AshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  

  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  Node sign_bit = utils::mkExtract(a, size-1, size-1);
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return n
    // repetitions of the first bit use repeat, which enables RARE
    // reconstruction to succeed
    return utils::mkRepeat(sign_bit, size);
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));

  uint32_t uint32_amount = amount.toUnsignedInt();
  if (uint32_amount == 0) {
    return a; 
  }

  Node left = utils::mkRepeat(sign_bit, uint32_amount);
  Node right = utils::mkExtract(a, size - 1, uint32_amount);
  return utils::mkConcat(left, right); 
}

/* -------------------------------------------------------------------------- */

/**
 * AndOrXorConcatPullUp
 *
 * Match:       x_m <op> concat(y_my, <const>_n, z_mz)
 *              <const>_n in { 0_n, 1_n, ~0_n }
 *
 * Rewrites to: concat(x[m-1:m-my]  <op> y,
 *                     x[m-my-1:mz] <op> <const>_n,
 *                     x[mz-1:0]    <op> z)
 */

template <>
inline bool RewriteRule<AndOrXorConcatPullUp>::applies(TNode node)
{
  if (node.getKind() != Kind::BITVECTOR_AND
      && node.getKind() != Kind::BITVECTOR_OR
      && node.getKind() != Kind::BITVECTOR_XOR)
  {
    return false;
  }

  TNode n;

  for (const TNode& c : node)
  {
    if (c.getKind() == Kind::BITVECTOR_CONCAT)
    {
      for (const TNode& cc : c)
      {
        if (cc.isConst())
        {
          n = cc;
          break;
        }
      }
      break;
    }
  }
  if (n.isNull()) return false;
  return utils::isZero(n) || utils::isOne(n) || utils::isOnes(n);
}

template <>
inline Node RewriteRule<AndOrXorConcatPullUp>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<AndOrXorConcatPullUp>(" << node << ")"
                      << std::endl;
  uint32_t m, my, mz;
  size_t nc;
  Kind kind = node.getKind();
  TNode concat;
  Node x, y, z, c;
  NodeManager* nm = node.getNodeManager();
  NodeBuilder xb(nm, kind);
  NodeBuilder yb(nm, Kind::BITVECTOR_CONCAT);
  NodeBuilder zb(nm, Kind::BITVECTOR_CONCAT);
  NodeBuilder res(nm, Kind::BITVECTOR_CONCAT);

  for (const TNode& child : node)
  {
    if (concat.isNull() && child.getKind() == Kind::BITVECTOR_CONCAT)
    {
      concat = child;
    }
    else
    {
      xb << child;
    }
  }
  x = xb.getNumChildren() > 1 ? xb.constructNode() : xb[0];

  for (const TNode& child : concat)
  {
    if (c.isNull())
    {
      if (utils::isZero(child) || utils::isOne(child) || utils::isOnes(child))
      {
        c = child;
      }
      else
      {
        yb << child;
      }
    }
    else
    {
      zb << child;
    }
  }
  Assert(!c.isNull());
  Assert(yb.getNumChildren() || zb.getNumChildren());

  if ((nc = yb.getNumChildren()) > 0)
  {
    y = nc > 1 ? yb.constructNode() : yb[0];
  }
  if ((nc = zb.getNumChildren()) > 0)
  {
    z = nc > 1 ? zb.constructNode() : zb[0];
  }
  m = utils::getSize(x);
#ifdef CVC5_ASSERTIONS
  uint32_t n = utils::getSize(c);
#endif
  my = y.isNull() ? 0 : utils::getSize(y);
  mz = z.isNull() ? 0 : utils::getSize(z);
  Assert(mz == m - my - n);
  Assert(my || mz);

  if (my)
  {
    res << nm->mkNode(kind, utils::mkExtract(x, m - 1, m - my), y);
  }

  res << nm->mkNode(kind, utils::mkExtract(x, m - my - 1, mz), c);

  if (mz)
  {
    res << nm->mkNode(kind, utils::mkExtract(x, mz - 1, 0), z);
  }

  return res;
}

/* -------------------------------------------------------------------------- */

/**
 * XorOnes
 *
 * (a bvxor ~0) ==> ~a
 */

template <>
inline bool RewriteRule<XorOnes>::applies(TNode node)
{
  if (node.getKind() != Kind::BITVECTOR_XOR)
  {
    return false;
  }
  NodeManager* nm = node.getNodeManager();
  Node ones = utils::mkOnes(nm, utils::getSize(node));
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i] == ones) {
      return true; 
    }
  }
  return false;
}

template <>
inline Node RewriteRule<XorOnes>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<XorOnes>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  Node ones = utils::mkOnes(nm, utils::getSize(node));
  std::vector<Node> children;
  bool found_ones = false;
  // XorSimplify should have been called before
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    if (node[i] == ones)
    {
      // make sure only ones occurs only once
      found_ones = !found_ones;
    }
    else
    {
      children.push_back(node[i]);
    }
  }

  Node result = utils::mkNaryNode(nm, Kind::BITVECTOR_XOR, children);
  if (found_ones)
  {
    result = NodeManager::mkNode(Kind::BITVECTOR_NOT, result);
  }
  return result;
}

/* -------------------------------------------------------------------------- */

/**
 * XorZero
 *
 * (a bvxor 0) ==> a
 */

template<> inline
bool RewriteRule<XorZero>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_XOR)
  {
    return false;
  }
  NodeManager* nm = node.getNodeManager();
  Node zero = utils::mkConst(nm, utils::getSize(node), 0);
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i] == zero) {
      return true; 
    }
  }
  return false; 
}

template <>
inline Node RewriteRule<XorZero>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<XorZero>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  std::vector<Node> children;
  Node zero = utils::mkConst(nm, utils::getSize(node), 0);

  // XorSimplify should have been called before
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    if (node[i] != zero)
    {
      children.push_back(node[i]);
    }
  }
  Node res = utils::mkNaryNode(nm, Kind::BITVECTOR_XOR, children);
  return res;
}

/* -------------------------------------------------------------------------- */

/**
 * NotIdemp
 *
 * ~ (~ a) ==> a
 */

template<> inline
bool RewriteRule<NotIdemp>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_NOT
          && node[0].getKind() == Kind::BITVECTOR_NOT);
}

template<> inline
Node RewriteRule<NotIdemp>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<NotIdemp>(" << node << ")" << std::endl;
  TNode ret = node[0][0];
  while (ret.getKind() == Kind::BITVECTOR_NOT
         && ret[0].getKind() == Kind::BITVECTOR_NOT)
  {
    ret = ret[0][0];
  }
  return ret;
}

/* -------------------------------------------------------------------------- */

/**
 * UltZero
 *
 * match:  (bvult (_ bv0 N) a)
 * result: (distinct (_ bv0 N) a)
 *
 * match:  (bvult a (_ bv0 N))
 * result: false
 */

template<> inline
bool RewriteRule<UltZero>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_ULT
          && (utils::isZero(node[0]) || utils::isZero(node[1])));
}

template<> inline
Node RewriteRule<UltZero>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UltZero>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  if (utils::isZero(node[1]))
  {
    return utils::mkFalse(nm);
  }
  return NodeManager::mkNode(
      Kind::DISTINCT, utils::mkZero(nm, utils::getSize(node[0])), node[1]);
}


/* -------------------------------------------------------------------------- */

/**
 * UltOne
 *
 * match:  (bvult a (_ bv1 N))
 * result: (= a (_ bv0 N))
 */
template <>
inline bool RewriteRule<UltOne>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ULT && utils::isOne(node[1]));
}

template <>
inline Node RewriteRule<UltOne>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UltOne>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  return NodeManager::mkNode(
      Kind::EQUAL, node[0], utils::mkZero(nm, utils::getSize(node[0])));
}

/* -------------------------------------------------------------------------- */

/**
 * UltOnes
 *
 * match:  (bvult (bvnot (_ bv0 N)) a)
 * result: false
 *
 * match:  (bvult a (bvnot (_ bv0 N)))
 * result: (distinct a (bvnot (_ bv0 N)))
 */
template <>
inline bool RewriteRule<UltOnes>::applies(TNode node)
{
  return node.getKind() == Kind::BITVECTOR_ULT
         && (utils::isOnes(node[0]) || utils::isOnes(node[1]));
}

template <>
inline Node RewriteRule<UltOnes>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UltOnes>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  if (utils::isOnes(node[1]))
  {
    return NodeManager::mkNode(
        Kind::DISTINCT, node[0], utils::mkOnes(nm, utils::getSize(node[1])));
  }
  return nm->mkConst(false);
}

/* -------------------------------------------------------------------------- */

/**
 * UltSelf
 *
 * a < a ==> false
 */

template<> inline
bool RewriteRule<UltSelf>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_ULT && node[1] == node[0]);
}

template<> inline
Node RewriteRule<UltSelf>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UltSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(node.getNodeManager());
}


/* -------------------------------------------------------------------------- */

/**
 * UleZero
 *
 * a <= 0 ==> a = 0
 */

template<> inline
bool RewriteRule<UleZero>::applies(TNode node) {
  NodeManager* nm = node.getNodeManager();
  return (node.getKind() == Kind::BITVECTOR_ULE
          && node[1] == utils::mkZero(nm, utils::getSize(node[0])));
}

template <>
inline Node RewriteRule<UleZero>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UleZero>(" << node << ")" << std::endl;
  return NodeManager::mkNode(Kind::EQUAL, node[0], node[1]);
}

/* -------------------------------------------------------------------------- */

/**
 * UleSelf
 *
 * a <= a ==> true
 */

template<> inline
bool RewriteRule<UleSelf>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_ULE && node[1] == node[0]);
}

template<> inline
Node RewriteRule<UleSelf>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UleSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(node.getNodeManager());
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroUle
 *
 * 0 <= a ==> true
 */

template<> inline
bool RewriteRule<ZeroUle>::applies(TNode node) {
  NodeManager* nm = node.getNodeManager();
  return (node.getKind() == Kind::BITVECTOR_ULE
          && node[0] == utils::mkZero(nm, utils::getSize(node[0])));
}

template<> inline
Node RewriteRule<ZeroUle>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ZeroUle>(" << node << ")" << std::endl;
  return utils::mkTrue(node.getNodeManager());
}

/* -------------------------------------------------------------------------- */

/**
 * UleMax
 *
 * a <= 11..1 ==> true
 */

template<> inline
bool RewriteRule<UleMax>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_ULE)
  {
    return false;
  }
  uint32_t size = utils::getSize(node[0]);
  NodeManager* nm = node.getNodeManager();
  return (node.getKind() == Kind::BITVECTOR_ULE
          && node[1] == utils::mkOnes(nm, size));
}

template<> inline
Node RewriteRule<UleMax>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UleMax>(" << node << ")" << std::endl;
  return utils::mkTrue(node.getNodeManager());
}

/* -------------------------------------------------------------------------- */

/**
 * SltSelf
 *
 * a < a ==> false
 */

template<> inline
bool RewriteRule<SltSelf>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_SLT && node[1] == node[0]);
}

template<> inline
Node RewriteRule<SltSelf>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<SltSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(node.getNodeManager());
}

/* -------------------------------------------------------------------------- */

/**
 * MultPow2
 *
 * (a * 2^k) ==> a[n-k-1:0] 0_k
 */

template <>
inline bool RewriteRule<MultPow2>::applies(TNode node)
{
  if (node.getKind() != Kind::BITVECTOR_MULT) return false;

  for (const Node& cn : node)
  {
    bool cIsNeg = false;
    if (utils::isPow2Const(cn, cIsNeg))
    {
      return true; 
    }
  }
  return false; 
}

template <>
inline Node RewriteRule<MultPow2>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<MultPow2>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  unsigned size = utils::getSize(node);
  std::vector<Node>  children;
  unsigned exponent = 0;
  bool isNeg = false;
  for (const Node& cn : node)
  {
    bool cIsNeg = false;
    unsigned exp = utils::isPow2Const(cn, cIsNeg);
    if (exp) {
      exponent += exp - 1;
      if (cIsNeg)
      {
        isNeg = !isNeg;
      }
    }
    else {
      children.push_back(cn);
    }
  }
  if (exponent >= size)
  {
    return utils::mkZero(nm, size);
  }

  Node a;
  if (children.empty())
  {
    a = utils::mkOne(nm, size);
  }
  else
  {
    a = utils::mkNaryNode(nm, Kind::BITVECTOR_MULT, children);
  }

  if (isNeg && size > 1)
  {
    a = NodeManager::mkNode(Kind::BITVECTOR_NEG, a);
  }
  if (exponent == 0)
  {
    return a;
  }
  Node extract = utils::mkExtract(a, size - exponent - 1, 0);
  Node zeros = utils::mkConst(nm, exponent, 0);
  return utils::mkConcat(extract, zeros); 
}

/* -------------------------------------------------------------------------- */

/**
 * ExtractMultLeadingBit
 *
 * If the bit-vectors multiplied have enough leading zeros,
 * we can determine that the top bits of the multiplication
 * are zero and not compute them. Only apply for large bitwidths
 * as this can interfere with other mult normalization rewrites such
 * as flattening. 
 */

template<> inline
bool RewriteRule<ExtractMultLeadingBit>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_EXTRACT) return false;
  unsigned low = utils::getExtractLow(node);
  node = node[0];

  if (node.getKind() != Kind::BITVECTOR_MULT || node.getNumChildren() != 2
      || utils::getSize(node) <= 64)
    return false;

  if (node[0].getKind() != Kind::BITVECTOR_CONCAT
      || node[1].getKind() != Kind::BITVECTOR_CONCAT || !node[0][0].isConst()
      || !node[1][0].isConst())
    return false;

  unsigned n = utils::getSize(node);
  // count number of leading zeroes
  const Integer& int1 = node[0][0].getConst<BitVector>().toInteger();
  const Integer& int2 = node[1][0].getConst<BitVector>().toInteger();
  size_t int1_size = utils::getSize(node[0][0]);
  size_t int2_size = utils::getSize(node[1][0]);
  unsigned zeroes1 = int1.isZero() ? int1_size : int1_size - int1.length();
  unsigned zeroes2 = int2.isZero() ? int2_size : int2_size - int2.length();

  // first k bits are not zero in the result
  unsigned k = 2 * n - (zeroes1 + zeroes2);

  if (k > low)
    return false; 

  return true; 
}

template<> inline
Node RewriteRule<ExtractMultLeadingBit>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<MultLeadingBit>(" << node << ")" << std::endl;

  unsigned bitwidth = utils::getSize(node); 
  
  // node = node[0];
  // const Integer& int1 = node[0][0].getConst<BitVector>().toInteger();
  // const Integer& int2 = node[1][0].getConst<BitVector>().toInteger();
  // unsigned zeroes1 = int1.isZero()? utils::getSize(node[0][0]) :
  //                                   int1.length();

  // unsigned zeroes2 = int2.isZero()? utils::getSize(node[1][0]) :
  //                                   int2.length();
  // all bits >= k in the multiplier will have to be 0
  // unsigned n = utils::getSize(node); 
  // unsigned k = 2 * n - (zeroes1 + zeroes2);
  // Node extract1 = utils::mkExtract(node[0], k - 1, 0);
  // Node extract2 = utils::mkExtract(node[1], k - 1, 0);
  // Node k_zeroes = utils::mkConst(n - k, 0u);

  // NodeManager *nm = node.getNodeManager();
  // Node new_mult = nm->mkNode(Kind::BITVECTOR_MULT, extract1, extract2);
  // Node result = utils::mkExtract(nm->mkNode(Kind::BITVECTOR_CONCAT, k_zeroes,
  // new_mult), high, low);

  // since the extract is over multiplier bits that have to be 0, return 0
  NodeManager* nm = node.getNodeManager();
  Node result = utils::mkConst(nm, bitwidth, 0u);
  //  std::cout << "MultLeadingBit " << node <<" => " << result <<"\n";
  return result;
}

/* -------------------------------------------------------------------------- */

/**
 * NegIdemp
 *
 * -(-a) ==> a 
 */

template<> inline
bool RewriteRule<NegIdemp>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_NEG
          && node[0].getKind() == Kind::BITVECTOR_NEG);
}

template<> inline
Node RewriteRule<NegIdemp>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<NegIdemp>(" << node << ")" << std::endl;
  return node[0][0]; 
}

/* -------------------------------------------------------------------------- */

/**
 * UdivPow2 
 *
 * (a udiv 2^k) ==> 0_k a[n-1: k]
 */

template <>
inline bool RewriteRule<UdivPow2>::applies(TNode node)
{
  bool isNeg = false;
  if (node.getKind() == Kind::BITVECTOR_UDIV
      && utils::isPow2Const(node[1], isNeg))
  {
    return !isNeg;
  }
  return false;
}

template <>
inline Node RewriteRule<UdivPow2>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UdivPow2>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  unsigned size = utils::getSize(node);
  Node a = node[0];
  bool isNeg = false;
  unsigned power = utils::isPow2Const(node[1], isNeg) - 1;
  Node ret;
  if (power == 0)
  {
    ret = a;
  }
  else
  {
    Node extract = utils::mkExtract(a, size - 1, power);
    Node zeros = utils::mkConst(nm, power, 0);

    ret = NodeManager::mkNode(Kind::BITVECTOR_CONCAT, zeros, extract);
  }
  if (isNeg && size > 1)
  {
    ret = NodeManager::mkNode(Kind::BITVECTOR_NEG, ret);
  }
  return ret;
}

/* -------------------------------------------------------------------------- */

/**
 * UdivZero
 *
 * (a udiv 0) ==> 111...1
 */

template <>
inline bool RewriteRule<UdivZero>::applies(TNode node) {
  NodeManager* nm = node.getNodeManager();
  return (node.getKind() == Kind::BITVECTOR_UDIV
          && node[1] == utils::mkConst(nm, utils::getSize(node), 0));
}

template <>
inline Node RewriteRule<UdivZero>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UdivZero>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  return utils::mkOnes(nm, utils::getSize(node));
}

/* -------------------------------------------------------------------------- */

/**
 * UdivOne
 *
 * (a udiv 1) ==> a
 */

template <>
inline bool RewriteRule<UdivOne>::applies(TNode node) {
  NodeManager* nm = node.getNodeManager();
  return (node.getKind() == Kind::BITVECTOR_UDIV
          && node[1] == utils::mkConst(nm, utils::getSize(node), 1));
}

template <>
inline Node RewriteRule<UdivOne>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UdivOne>(" << node << ")" << std::endl;
  return node[0];
}

/* -------------------------------------------------------------------------- */

/**
 * UremPow2
 *
 * (a urem 2^k) ==> 0_(n-k) a[k-1:0]
 */

template <>
inline bool RewriteRule<UremPow2>::applies(TNode node)
{
  bool isNeg;
  if (node.getKind() == Kind::BITVECTOR_UREM
      && utils::isPow2Const(node[1], isNeg))
  {
    return !isNeg;
  }
  return false;
}

template <>
inline Node RewriteRule<UremPow2>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UremPow2>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  TNode a = node[0];
  bool isNeg = false;
  unsigned power = utils::isPow2Const(node[1], isNeg) - 1;
  Node ret;
  if (power == 0)
  {
    ret = utils::mkZero(nm, utils::getSize(node));
  }
  else
  {
    Node extract = utils::mkExtract(a, power - 1, 0);
    Node zeros = utils::mkZero(nm, utils::getSize(node) - power);
    ret = NodeManager::mkNode(Kind::BITVECTOR_CONCAT, zeros, extract);
  }
  return ret;
}

/* -------------------------------------------------------------------------- */

/**
 * UremOne
 *
 * (a urem 1) ==> 0
 */

template<> inline
bool RewriteRule<UremOne>::applies(TNode node) {
  NodeManager* nm = node.getNodeManager();
  return (node.getKind() == Kind::BITVECTOR_UREM
          && node[1] == utils::mkConst(nm, utils::getSize(node), 1));
}

template<> inline
Node RewriteRule<UremOne>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UremOne>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  return utils::mkConst(nm, utils::getSize(node), 0);
}

/* -------------------------------------------------------------------------- */

/**
 * UremSelf 
 *
 * (a urem a) ==> 0
 */

template<> inline
bool RewriteRule<UremSelf>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_UREM && node[0] == node[1]);
}

template<> inline
Node RewriteRule<UremSelf>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UremSelf>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  return utils::mkConst(nm, utils::getSize(node), 0);
}

/* -------------------------------------------------------------------------- */

/**
 * ShiftZero
 *
 * (0_k >> a) ==> 0_k 
 */

template<> inline
bool RewriteRule<ShiftZero>::applies(TNode node) {
  NodeManager* nm = node.getNodeManager();
  return ((node.getKind() == Kind::BITVECTOR_SHL
           || node.getKind() == Kind::BITVECTOR_LSHR
           || node.getKind() == Kind::BITVECTOR_ASHR)
          && node[0] == utils::mkConst(nm, utils::getSize(node), 0));
}

template<> inline
Node RewriteRule<ShiftZero>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ShiftZero>(" << node << ")" << std::endl;
  return node[0]; 
}

/* -------------------------------------------------------------------------- */

/**
 * UgtUrem
 *
 * (bvugt (bvurem T x) x)
 *   ==>  (ite (= x 0_k) (bvugt T x) false)
 *   ==>  (and (=> (= x 0_k) (bvugt T x)) (=> (not (= x 0_k)) false))
 *   ==>  (and (=> (= x 0_k) (bvugt T x)) (= x 0_k))
 *   ==>  (and (bvugt T x) (= x 0_k))
 *   ==>  (and (bvugt T 0_k) (= x 0_k))
 */

template <>
inline bool RewriteRule<UgtUrem>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_UGT
          && node[0].getKind() == Kind::BITVECTOR_UREM
          && node[0][1] == node[1]);
}

template <>
inline Node RewriteRule<UgtUrem>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UgtUrem>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  const Node& T = node[0][0];
  const Node& x = node[1];
  Node zero = utils::mkConst(nm, utils::getSize(x), 0);
  return NodeManager::mkNode(Kind::AND,
                             NodeManager::mkNode(Kind::EQUAL, x, zero),
                             NodeManager::mkNode(Kind::BITVECTOR_UGT, T, zero));
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<MergeSignExtend>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_SIGN_EXTEND
      || (node[0].getKind() != Kind::BITVECTOR_SIGN_EXTEND
          && node[0].getKind() != Kind::BITVECTOR_ZERO_EXTEND))
    return false;
  return true;
}

template<> inline
Node RewriteRule<MergeSignExtend>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<MergeSignExtend>(" << node << ")" << std::endl;
  unsigned amount1 =
      node.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;

  NodeManager* nm = node.getNodeManager();
  if (node[0].getKind() == Kind::BITVECTOR_ZERO_EXTEND)
  {
    unsigned amount2 = node[0]
                           .getOperator()
                           .getConst<BitVectorZeroExtend>()
                           .d_zeroExtendAmount;
    if (amount2 == 0)
    {
      NodeBuilder nb(nm, Kind::BITVECTOR_SIGN_EXTEND);
      Node op = nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(amount1));
      nb << op << node[0][0];
      Node res = nb;
      return res;
    }
    NodeBuilder nb(nm, Kind::BITVECTOR_ZERO_EXTEND);
    Node op = nm->mkConst<BitVectorZeroExtend>(
        BitVectorZeroExtend(amount1 + amount2));
    nb << op << node[0][0];
    Node res = nb;
    return res;
  }
  Assert(node[0].getKind() == Kind::BITVECTOR_SIGN_EXTEND);
  unsigned amount2 =
      node[0].getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;
  return utils::mkSignExtend(node[0][0], amount1 + amount2);
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroExtendEqConst
 *
 * Rewrite zero_extend(x^n, m) = c^n+m to
 *
 *   false         if c[n+m-1:n] != 0
 *   x = c[n-1:0]  otherwise.
 */
template <>
inline bool RewriteRule<ZeroExtendEqConst>::applies(TNode node) {
  return node.getKind() == Kind::EQUAL
         && ((node[0].getKind() == Kind::BITVECTOR_ZERO_EXTEND
              && node[1].isConst())
             || (node[1].getKind() == Kind::BITVECTOR_ZERO_EXTEND
                 && node[0].isConst()));
}

template <>
inline Node RewriteRule<ZeroExtendEqConst>::apply(TNode node) {
  NodeManager* nm = node.getNodeManager();
  TNode t, c;
  if (node[0].getKind() == Kind::BITVECTOR_ZERO_EXTEND)
  {
    t = node[0][0];
    c = node[1];
  }
  else
  {
    t = node[1][0];
    c = node[0];
  }
  BitVector c_hi =
      c.getConst<BitVector>().extract(utils::getSize(c) - 1, utils::getSize(t));
  BitVector c_lo = c.getConst<BitVector>().extract(utils::getSize(t) - 1, 0);
  BitVector zero = BitVector(c_hi.getSize(), Integer(0));

  if (c_hi == zero) {
    return NodeManager::mkNode(Kind::EQUAL, t, utils::mkConst(nm, c_lo));
  }
  return utils::mkFalse(node.getNodeManager());
}

/* -------------------------------------------------------------------------- */

/**
 * SignExtendEqConst
 *
 * Rewrite sign_extend(x^n, m) = c^n+m to
 *
 *   x = c[n-1:0]   if (c[n-1:n-1] == 0 && c[n+m-1:n] == 0) ||
 *                     (c[n-1:n-1] == 1 && c[n+m-1:n] == ~0)
 *   false          otherwise.
 */
template <>
inline bool RewriteRule<SignExtendEqConst>::applies(TNode node) {
  return node.getKind() == Kind::EQUAL
         && ((node[0].getKind() == Kind::BITVECTOR_SIGN_EXTEND
              && node[1].isConst())
             || (node[1].getKind() == Kind::BITVECTOR_SIGN_EXTEND
                 && node[0].isConst()));
}

template <>
inline Node RewriteRule<SignExtendEqConst>::apply(TNode node) {
  NodeManager* nm = node.getNodeManager();
  TNode t, c;
  if (node[0].getKind() == Kind::BITVECTOR_SIGN_EXTEND)
  {
    t = node[0][0];
    c = node[1];
  }
  else
  {
    t = node[1][0];
    c = node[0];
  }
  unsigned pos_msb_t = utils::getSize(t) - 1;
  BitVector c_hi =
      c.getConst<BitVector>().extract(utils::getSize(c) - 1, pos_msb_t);
  BitVector c_lo = c.getConst<BitVector>().extract(pos_msb_t, 0);
  BitVector zero = BitVector(c_hi.getSize(), Integer(0));

  if (c_hi == zero || c_hi == ~zero) {
    return NodeManager::mkNode(Kind::EQUAL, t, utils::mkConst(nm, c_lo));
  }
  return utils::mkFalse(node.getNodeManager());
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroExtendUltConst
 *
 * Rewrite zero_extend(x^n,m) < c^n+m to
 *
 *   x < c[n-1:0]   if c[n+m-1:n] == 0.
 *
 * Rewrite c^n+m < Rewrite zero_extend(x^n,m) to
 *
 *   c[n-1:0] < x   if c[n+m-1:n] == 0.
 */
template <>
inline bool RewriteRule<ZeroExtendUltConst>::applies(TNode node) {
  if (node.getKind() == Kind::BITVECTOR_ULT
      && ((node[0].getKind() == Kind::BITVECTOR_ZERO_EXTEND
           && node[1].isConst())
          || (node[1].getKind() == Kind::BITVECTOR_ZERO_EXTEND
              && node[0].isConst())))
  {
    TNode t, c;
    bool is_lhs = node[0].getKind() == Kind::BITVECTOR_ZERO_EXTEND;
    if (is_lhs) {
      t = node[0][0];
      c = node[1];
    } else {
      t = node[1][0];
      c = node[0];
    }

    if (utils::getSize(t) == utils::getSize(c))
    {
      return false;
    }

    BitVector bv_c = c.getConst<BitVector>();
    BitVector c_hi = c.getConst<BitVector>().extract(utils::getSize(c) - 1,
                                                     utils::getSize(t));
    BitVector zero = BitVector(c_hi.getSize(), Integer(0));

    return c_hi == zero;
  }
  return false;
}

template <>
inline Node RewriteRule<ZeroExtendUltConst>::apply(TNode node) {
  NodeManager* nm = node.getNodeManager();
  TNode t, c;
  bool is_lhs = node[0].getKind() == Kind::BITVECTOR_ZERO_EXTEND;
  if (is_lhs) {
    t = node[0][0];
    c = node[1];
  } else {
    t = node[1][0];
    c = node[0];
  }
  Node c_lo = utils::mkConst(
      nm, c.getConst<BitVector>().extract(utils::getSize(t) - 1, 0));

  if (is_lhs) {
    return NodeManager::mkNode(Kind::BITVECTOR_ULT, t, c_lo);
  }
  return NodeManager::mkNode(Kind::BITVECTOR_ULT, c_lo, t);
}

/* -------------------------------------------------------------------------- */

/**
 * SignExtendUltConst
 *
 * Rewrite sign_extend(x^n,m) < c^n+m to
 *
 *   x < c[n-1:0]   if (c <= (1 << (n - 1))) || (c >= (~0 << (n - 1)))
 *   x[n-1:n-1] = 0 if (1 << (n - 1)) < c <= (~0 << (n - 1)).
 *
 * Rewrite c^n+m < sign_extend(x^n,m) to
 *
 *   c[n-1:0] < x   if (c < (1 << (n - 1))) || (c >= ~(1 << (n-1)))
 *   x[n-1:n-1] = 1 if ~(~0 << (n-1)) <= c <= ~(1 << (n-1))
 *
 * where ~(~0 << (n - 1)) == (1 << (n - 1)) - 1
 *
 */
template <>
inline bool RewriteRule<SignExtendUltConst>::applies(TNode node)
{
  if (node.getKind() == Kind::BITVECTOR_ULT
      && ((node[0].getKind() == Kind::BITVECTOR_SIGN_EXTEND
           && node[1].isConst())
          || (node[1].getKind() == Kind::BITVECTOR_SIGN_EXTEND
              && node[0].isConst())))
  {
    TNode x, c;
    bool is_lhs = node[0].getKind() == Kind::BITVECTOR_SIGN_EXTEND;
    if (is_lhs)
    {
      x = node[0][0];
      c = node[1];
    }
    else
    {
      x = node[1][0];
      c = node[0];
    }
    BitVector bv_c = c.getConst<BitVector>();
    unsigned size_c = utils::getSize(c);
    unsigned msb_x_pos = utils::getSize(x) - 1;
    // (1 << (n - 1)))
    BitVector bv_msb_x(size_c);
    bv_msb_x.setBit(msb_x_pos, true);
    // (~0 << (n - 1))
    BitVector bv_upper_bits =
        (~BitVector(size_c)).leftShift(BitVector(size_c, msb_x_pos));

    return (is_lhs
            && (bv_c <= bv_msb_x || bv_c >= bv_upper_bits
                || (bv_msb_x < bv_c && bv_c <= bv_upper_bits)))
           || (!is_lhs
               && (bv_c < bv_msb_x || bv_c >= ~bv_msb_x
                   || (~bv_upper_bits <= bv_c && bv_c <= ~bv_msb_x)));
  }
  return false;
}

template <>
inline Node RewriteRule<SignExtendUltConst>::apply(TNode node)
{
  NodeManager* nm = node.getNodeManager();
  TNode x, c;
  bool is_lhs = node[0].getKind() == Kind::BITVECTOR_SIGN_EXTEND;
  if (is_lhs)
  {
    x = node[0][0];
    c = node[1];
  }
  else
  {
    x = node[1][0];
    c = node[0];
  }
  BitVector bv_c = c.getConst<BitVector>();

  unsigned size_c = utils::getSize(c);
  unsigned msb_x_pos = utils::getSize(x) - 1;
  Node c_lo = utils::mkConst(nm, bv_c.extract(msb_x_pos, 0));
  // (1 << (n - 1)))
  BitVector bv_msb_x(size_c);
  bv_msb_x.setBit(msb_x_pos, true);
  // (~0 << (n - 1))
  BitVector bv_upper_bits =
      (~BitVector(size_c)).leftShift(BitVector(size_c, msb_x_pos));

  if (is_lhs)
  {
    // x[n-1:n-1] = 0
    if (bv_msb_x < bv_c && bv_c <= bv_upper_bits)
    {
      Node msb_x = utils::mkExtract(x, msb_x_pos, msb_x_pos);
      return NodeManager::mkNode(Kind::EQUAL, msb_x, utils::mkZero(nm, 1));
    }
    // x < c[n-1:0]
    Assert(bv_c <= bv_msb_x || bv_c >= bv_upper_bits);
    return NodeManager::mkNode(Kind::BITVECTOR_ULT, x, c_lo);
  }

  // x[n-1:n-1] = 1
  if (~bv_upper_bits <= bv_c && bv_c <= ~bv_msb_x)
  {
    Node msb_x = utils::mkExtract(x, msb_x_pos, msb_x_pos);
    return NodeManager::mkNode(Kind::EQUAL, msb_x, utils::mkOne(nm, 1));
  }
  // c[n-1:0] < x
  Assert(bv_c < bv_msb_x || bv_c >= ~bv_msb_x);
  return NodeManager::mkNode(Kind::BITVECTOR_ULT, c_lo, x);
}

/* -------------------------------------------------------------------------- */

/**
 */
template <>
inline bool RewriteRule<IneqElimConversion>::applies(TNode node)
{
  Kind k = node.getKind();
  if (k == Kind::BITVECTOR_ULT || k == Kind::BITVECTOR_ULE
      || k == Kind::BITVECTOR_UGT || k == Kind::BITVECTOR_UGE)
  {
    for (const Node& nc : node)
    {
      Kind nck = nc.getKind();
      if (nck != Kind::INT_TO_BITVECTOR && nck != Kind::CONST_BITVECTOR)
      {
        return false;
      }
    }
    return true;
  }
  return false;
}

template <>
inline Node RewriteRule<IneqElimConversion>::apply(TNode node)
{
  NodeManager* nm = node.getNodeManager();
  std::vector<Node> children;
  for (const Node& nc : node)
  {
    Kind nck = nc.getKind();
    if (nck == Kind::INT_TO_BITVECTOR)
    {
      size_t bvSize = nc.getOperator().getConst<IntToBitVector>();
      Node w = nm->mkConstInt(Rational(Integer(2).pow(bvSize)));
      children.push_back(nm->mkNode(Kind::INTS_MODULUS, nc[0], w));
    }
    else
    {
      Assert(nck == Kind::CONST_BITVECTOR);
      children.push_back(nm->mkNode(Kind::BITVECTOR_UBV_TO_INT, nc));
    }
  }
  // E.g. (bvuge ((_ int2bv w) x) N) ---> (>= (mod x 2^w) (bv2nat N)).
  // Note that (bv2nat N) is subsequently rewritten to the appropriate integer
  // constant.
  Kind arithKind;
  switch (node.getKind())
  {
    case Kind::BITVECTOR_ULT: arithKind = Kind::LT; break;
    case Kind::BITVECTOR_ULE: arithKind = Kind::LEQ; break;
    case Kind::BITVECTOR_UGT: arithKind = Kind::GT; break;
    case Kind::BITVECTOR_UGE: arithKind = Kind::GEQ; break;
    default:
      Unhandled() << "Unknown kind for IneqElimConversion " << node;
      break;
  }
  return nm->mkNode(arithKind, children);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<MultSlice>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_MULT || node.getNumChildren() != 2)
  {
    return false;
  }
  return utils::getSize(node[0]) % 2 == 0;
}

/** 
 * Expressses the multiplication in terms of the top and bottom
 * slices of the terms. Note increases circuit size, but could
 * lead to simplifications (use wisely!).
 * 
 * @param node 
 * 
 * @return 
 */
template <>
inline Node RewriteRule<MultSlice>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<MultSlice>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  unsigned bitwidth = utils::getSize(node[0]);
  Node zeros = utils::mkConst(nm, bitwidth / 2, 0);
  TNode a = node[0];
  Node bottom_a = utils::mkExtract(a, bitwidth / 2 - 1, 0);
  Node top_a = utils::mkExtract(a, bitwidth - 1, bitwidth / 2);
  TNode b = node[1];
  Node bottom_b = utils::mkExtract(b, bitwidth / 2 - 1, 0);
  Node top_b = utils::mkExtract(b, bitwidth - 1, bitwidth / 2);

  Node term1 = NodeManager::mkNode(
      Kind::BITVECTOR_MULT,
      NodeManager::mkNode(Kind::BITVECTOR_CONCAT, zeros, bottom_a),
      NodeManager::mkNode(Kind::BITVECTOR_CONCAT, zeros, bottom_b));

  Node term2 = NodeManager::mkNode(
      Kind::BITVECTOR_CONCAT,
      NodeManager::mkNode(Kind::BITVECTOR_MULT, top_b, bottom_a),
      zeros);
  Node term3 = NodeManager::mkNode(
      Kind::BITVECTOR_CONCAT,
      NodeManager::mkNode(Kind::BITVECTOR_MULT, top_a, bottom_b),
      zeros);
  return NodeManager::mkNode(Kind::BITVECTOR_ADD, term1, term2, term3);
}

/* -------------------------------------------------------------------------- */

/** 
 * x < y + 1 <=> (not y < x) and y != 1...1
 * 
 * @param node 
 * 
 * @return 
 */
template <>
inline bool RewriteRule<UltAddOne>::applies(TNode node)
{
  if (node.getKind() != Kind::BITVECTOR_ULT) return false;
  TNode x = node[0];
  TNode y1 = node[1];
  if (y1.getKind() != Kind::BITVECTOR_ADD) return false;
  if (y1[0].getKind() != Kind::CONST_BITVECTOR
      && y1[1].getKind() != Kind::CONST_BITVECTOR)
    return false;

  if (y1[0].getKind() == Kind::CONST_BITVECTOR
      && y1[1].getKind() == Kind::CONST_BITVECTOR)
    return false;

  if (y1.getNumChildren() != 2) return false;

  TNode one = y1[0].getKind() == Kind::CONST_BITVECTOR ? y1[0] : y1[1];
  NodeManager* nm = node.getNodeManager();
  if (one != utils::mkConst(nm, utils::getSize(one), 1)) return false;
  return true;
}

template <>
inline Node RewriteRule<UltAddOne>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UltAddOne>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  TNode x = node[0];
  TNode y1 = node[1];
  TNode y = y1[0].getKind() != Kind::CONST_BITVECTOR ? y1[0] : y1[1];
  unsigned size = utils::getSize(x);
  Node not_y_eq_1 = NodeManager::mkNode(
      Kind::NOT, NodeManager::mkNode(Kind::EQUAL, y, utils::mkOnes(nm, size)));
  Node not_y_lt_x = NodeManager::mkNode(
      Kind::NOT, NodeManager::mkNode(Kind::BITVECTOR_ULT, y, x));
  return NodeManager::mkNode(Kind::AND, not_y_eq_1, not_y_lt_x);
}

/* -------------------------------------------------------------------------- */

/**
 * MultSltMult
 *
 * Rewrite
 *   sign_extend(x+t,n) * sign_extend(a,m) < sign_extend(x,n) * sign_extend(a,m)
 * to
 *   (and
 *    (not (= t zero))
 *    (not (= a zero))
 *    (= (bvslt (bvadd x t) x) (bvsgt a zero))
 *   )
 *
 * Rewrite
 *   zero_extend(x+t,n) * sign_extend(a,m) < zero_extend(x,n) * sign_extend(a,m)
 * to
 *   (and
 *    (not (= t zero))
 *    (not (= a zero))
 *    (= (bvult (bvadd x t) x) (bvsgt a zero))
 *   )
 * where n and m are sufficiently big to not produce an overflow for
 * the multiplications.
 *
 * These patterns occur in the quantified BV benchmark family 'ranking',
 * where the BV engine struggles due to the high bit widths of the
 * multiplication's operands.
 */

namespace {
std::tuple<Node, Node, bool> extract_ext_tuple(TNode node)
{
  NodeManager* nm = node.getNodeManager();
  TNode a = node[0];
  TNode b = node[1];
  for (unsigned i = 0; i < 2; ++i)
  {
    if (a.getKind() == Kind::BITVECTOR_CONCAT
        && b.getKind() == Kind::BITVECTOR_SIGN_EXTEND
        && a[0] == utils::mkZero(nm, utils::getSize(a[0]))
        && utils::getSize(a[1]) <= utils::getSize(a[0])
        && utils::getSize(b[0]) <= utils::getSignExtendAmount(b))
    {
      return std::make_tuple(a[1], b[0], false);
    }
    else if (i == 0 && a.getKind() == Kind::BITVECTOR_SIGN_EXTEND
             && b.getKind() == Kind::BITVECTOR_SIGN_EXTEND
             && utils::getSize(a[0]) <= utils::getSignExtendAmount(a)
             && utils::getSize(b[0]) <= utils::getSignExtendAmount(b))
    {
      return std::make_tuple(a[0], b[0], true);
    }
    std::swap(a, b);
  }
  return std::make_tuple(Node::null(), Node::null(), false);
}
}  // namespace

template<> inline
bool RewriteRule<MultSltMult>::applies(TNode node)
{
  if (node.getKind() != Kind::BITVECTOR_SLT
      || node[0].getKind() != Kind::BITVECTOR_MULT
      || node[1].getKind() != Kind::BITVECTOR_MULT)
    return false;

  if (node[0].getNumChildren() > 2 || node[1].getNumChildren() > 2)
    return false;

  bool is_sext_l, is_sext_r;
  TNode ml[2], mr[2];

  std::tie(ml[0], ml[1], is_sext_l) = extract_ext_tuple(node[0]);
  if (ml[0].isNull())
    return false;

  std::tie(mr[0], mr[1], is_sext_r) = extract_ext_tuple(node[1]);
  if (mr[0].isNull())
    return false;

  if (is_sext_l != is_sext_r)
    return false;

  TNode addxt, x, a;
  if (ml[0].getKind() == Kind::BITVECTOR_ADD)
  {
    addxt = ml[0];
    a = ml[1];
  }
  else if (ml[1].getKind() == Kind::BITVECTOR_ADD)
  {
    addxt = ml[1];
    a = ml[0];
  }
  else
    return false;

  if (addxt.getNumChildren() > 2)
    return false;

  if (mr[0] == a)
  {
    x = mr[1];
  }
  else if (mr[1] == a)
  {
    x = mr[0];
  }
  else
    return false;

  return (addxt[0] == x || addxt[1] == x);
}

template<> inline
Node RewriteRule<MultSltMult>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<MultSltMult>(" << node << ")"
                      << std::endl;
  bool is_sext;
  TNode ml[2], mr[2];

  std::tie(ml[0], ml[1], is_sext) = extract_ext_tuple(node[0]);
  std::tie(mr[0], mr[1], std::ignore) = extract_ext_tuple(node[1]);

  TNode addxt, x, a;
  if (ml[0].getKind() == Kind::BITVECTOR_ADD)
  {
    addxt = ml[0];
    a = ml[1];
  }
  else
  {
    Assert(ml[1].getKind() == Kind::BITVECTOR_ADD);
    addxt = ml[1];
    a = ml[0];
  }

  x = (mr[0] == a) ? mr[1] : mr[0];
  // Make the subtraction term (bvsub (bvadd x t) x) or (bvsub (bvadd t x) x),
  // which will simplify to t. We use this instead of t to simplify the number
  // of cases needed for proof reconstruction.
  NodeManager* nm = node.getNodeManager();
  Node t = nm->mkNode(Kind::BITVECTOR_SUB, addxt, x);
  Node zero_t = utils::mkZero(nm, utils::getSize(t));
  Node zero_a = utils::mkZero(nm, utils::getSize(a));

  NodeBuilder nb(nm, Kind::AND);
  Kind k = is_sext ? Kind::BITVECTOR_SLT : Kind::BITVECTOR_ULT;
  nb << t.eqNode(zero_t).notNode();
  nb << a.eqNode(zero_a).notNode();
  nb << nm->mkNode(k, addxt, x)
            .eqNode(nm->mkNode(Kind::BITVECTOR_SGT, a, zero_a));
  Node ret = nb.constructNode();
  Trace("bv-rewrite") << "RewriteRule<MultSltMult>(" << ret << ")" << std::endl;
  return ret;
}

/* -------------------------------------------------------------------------- */
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif
