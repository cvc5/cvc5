/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 * BitOfConst
 */
template <>
inline bool RewriteRule<BitOfConst>::applies(TNode node)
{
  return node.getKind() == kind::BITVECTOR_BITOF && node[0].isConst();
}

template <>
inline Node RewriteRule<BitOfConst>::apply(TNode node)
{
  size_t pos = node.getOperator().getConst<BitVectorBitOf>().d_bitIndex;
  return utils::getBit(node[0], pos) ? utils::mkTrue() : utils::mkFalse();
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
  return (node.getKind() == kind::BITVECTOR_ITE && node[0].isConst());
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
  return (node.getKind() == kind::BITVECTOR_ITE && node[1] == node[2]);
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
  return (node.getKind() == kind::BITVECTOR_ITE
          && utils::getSize(node[1]) == 1
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
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_NOT, node[0]);
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
      node.getKind() == kind::BITVECTOR_ITE
      && ((node[1].getKind() == kind::BITVECTOR_ITE && node[0] == node[1][0])
          || (node[2].getKind() == kind::BITVECTOR_ITE
              && node[0] == node[2][0])));
}

template <>
inline Node RewriteRule<BvIteEqualCond>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteEqualCond>(" << node << ")"
                      << std::endl;
  Node t0 = node[1].getKind() == kind::BITVECTOR_ITE && node[0] == node[1][0]
                ? node[1][1]
                : node[1];
  Node e1 = node[2].getKind() == kind::BITVECTOR_ITE && node[0] == node[2][0]
                ? node[2][2]
                : node[2];
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_ITE, node[0], t0, e1);
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
  return (node.getKind() == kind::BITVECTOR_ITE
          && node[1].getKind() == kind::BITVECTOR_ITE
          && node[1][1] == node[2]);
}

template <>
inline Node RewriteRule<BvIteMergeThenIf>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeThenIf>(" << node << ")"
                      << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Assert(node[1].getKind() == kind::BITVECTOR_ITE);
  Node cond = nm->mkNode(kind::BITVECTOR_AND,
                         node[0],
                         nm->mkNode(kind::BITVECTOR_NOT, node[1][0]));
  return nm->mkNode(kind::BITVECTOR_ITE, cond, node[1][2], node[2]);
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
  return (node.getKind() == kind::BITVECTOR_ITE
          && node[1].getKind() == kind::BITVECTOR_ITE
          && node[1][2] == node[2]);
}

template <>
inline Node RewriteRule<BvIteMergeElseIf>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeElseIf>(" << node << ")"
                      << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Assert(node[1].getKind() == kind::BITVECTOR_ITE);
  Node cond = nm->mkNode(kind::BITVECTOR_AND, node[0], node[1][0]);
  return nm->mkNode(kind::BITVECTOR_ITE, cond, node[1][1], node[2]);
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
  return (node.getKind() == kind::BITVECTOR_ITE
          && node[2].getKind() == kind::BITVECTOR_ITE
          && node[1] == node[2][1]);
}

template <>
inline Node RewriteRule<BvIteMergeThenElse>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeThenElse>(" << node << ")"
                      << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Assert(node[2].getKind() == kind::BITVECTOR_ITE);
  Node cond = nm->mkNode(kind::BITVECTOR_AND,
                         nm->mkNode(kind::BITVECTOR_NOT, node[0]),
                         nm->mkNode(kind::BITVECTOR_NOT, node[2][0]));
  return nm->mkNode(kind::BITVECTOR_ITE, cond, node[2][2], node[1]);
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
  return (node.getKind() == kind::BITVECTOR_ITE
          && node[2].getKind() == kind::BITVECTOR_ITE
          && node[1] == node[2][2]);
}

template <>
inline Node RewriteRule<BvIteMergeElseElse>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvIteMergeElseElse>(" << node << ")"
                      << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Assert(node[2].getKind() == kind::BITVECTOR_ITE);
  Node cond = nm->mkNode(kind::BITVECTOR_AND,
                         nm->mkNode(kind::BITVECTOR_NOT, node[0]),
                         node[2][0]);
  return nm->mkNode(kind::BITVECTOR_ITE, cond, node[2][1], node[1]);
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
  return (node.getKind() == kind::BITVECTOR_COMP
          && utils::getSize(node[0]) == 1
          && (node[0].isConst() || node[1].isConst()));
}

template <>
inline Node RewriteRule<BvComp>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BvComp>(" << node << ")" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  if (node[0].isConst())
  {
    return utils::isZero(node[0]) ? nm->mkNode(kind::BITVECTOR_NOT, node[1])
                                  : Node(node[1]);
  }
  return utils::isZero(node[1]) ? nm->mkNode(kind::BITVECTOR_NOT, node[0])
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
  return (node.getKind() == kind::BITVECTOR_SHL &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<ShlByConst>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ShlByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkZero(size);
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));

  uint32_t uint32_amount = amount.toUnsignedInt();

  Node left = utils::mkExtract(a, size - 1 - uint32_amount, 0);
  Node right = utils::mkZero(uint32_amount);
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
  return (node.getKind() == kind::BITVECTOR_LSHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
}

template<> inline
Node RewriteRule<LshrByConst>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<LshrByConst>(" << node << ")" << std::endl;
  Integer amount = node[1].getConst<BitVector>().toInteger();
  if (amount == 0) {
    return node[0]; 
  }  
  
  Node a = node[0]; 
  uint32_t size = utils::getSize(a);
  
  
  if (amount >= Integer(size)) {
    // if we are shifting more than the length of the bitvector return 0
    return utils::mkZero(size);
  }
  
  // make sure we do not lose information casting
  Assert(amount < Integer(1).multiplyByPow2(32));

  uint32_t uint32_amount = amount.toUnsignedInt();
  Node right = utils::mkExtract(a, size - 1, uint32_amount);
  Node left = utils::mkZero(uint32_amount);
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
  return (node.getKind() == kind::BITVECTOR_ASHR &&
          node[1].getKind() == kind::CONST_BITVECTOR);
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

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<BitwiseIdemp>(" << node << ")" << std::endl;
  return node[0]; 
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<AndZero>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<AndOne>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node);
  
  if (node[0] == utils::mkOnes(size)) {
    return node[1]; 
  } else {
    Assert(node[1] == utils::mkOnes(size));
    return node[0]; 
  }
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
  if (node.getKind() != kind::BITVECTOR_AND
      && node.getKind() != kind::BITVECTOR_OR
      && node.getKind() != kind::BITVECTOR_XOR)
  {
    return false;
  }

  TNode n;

  for (const TNode& c : node)
  {
    if (c.getKind() == kind::BITVECTOR_CONCAT)
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
  NodeBuilder xb(kind);
  NodeBuilder yb(kind::BITVECTOR_CONCAT);
  NodeBuilder zb(kind::BITVECTOR_CONCAT);
  NodeBuilder res(kind::BITVECTOR_CONCAT);
  NodeManager* nm = NodeManager::currentNM();

  for (const TNode& child : node)
  {
    if (concat.isNull() && child.getKind() == kind::BITVECTOR_CONCAT)
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
  Trace("bv-rewrite") << "RewriteRule<OrZero>(" << node << ")" << std::endl;
  
  unsigned size = utils::getSize(node); 
  if (node[0] == utils::mkConst(size, 0)) {
    return node[1]; 
  } else {
    Assert(node[1] == utils::mkConst(size, 0));
    return node[0]; 
  }
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<OrOne>(" << node << ")" << std::endl;
  return utils::mkOnes(utils::getSize(node)); 
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<XorDuplicate>(" << node << ")" << std::endl;
  return utils::mkZero(utils::getSize(node));
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

template <>
inline Node RewriteRule<XorOnes>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<XorOnes>(" << node << ")" << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  Node ones = utils::mkOnes(utils::getSize(node));
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

  Node result = utils::mkNaryNode(kind::BITVECTOR_XOR, children);
  if (found_ones)
  {
    result = nm->mkNode(kind::BITVECTOR_NOT, result);
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

template <>
inline Node RewriteRule<XorZero>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<XorZero>(" << node << ")" << std::endl;
  std::vector<Node> children;
  Node zero = utils::mkConst(utils::getSize(node), 0);

  // XorSimplify should have been called before
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    if (node[i] != zero)
    {
      children.push_back(node[i]);
    }
  }
  Node res = utils::mkNaryNode(kind::BITVECTOR_XOR, children);
  return res;
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<BitwiseNegAnd>(" << node << ")" << std::endl;
  return utils::mkZero(utils::getSize(node));
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<BitwiseNotOr>(" << node << ")" << std::endl;
  uint32_t size = utils::getSize(node);
  return utils::mkOnes(size);
}

/* -------------------------------------------------------------------------- */

/**
 * XorNot
 *
 * ((~ a) bvxor (~ b)) ==> (a bvxor b)
 */

template<> inline
bool RewriteRule<XorNot>::applies(TNode node) {
  Unreachable();
}

template <>
inline Node RewriteRule<XorNot>::apply(TNode node)
{
  Unreachable();
  Trace("bv-rewrite") << "RewriteRule<XorNot>(" << node << ")" << std::endl;
  Node a = node[0][0];
  Node b = node[1][0];
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_XOR, a, b);
}

/* -------------------------------------------------------------------------- */

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

template <>
inline Node RewriteRule<NotXor>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NotXor>(" << node << ")" << std::endl;
  std::vector<Node> children;
  TNode::iterator child_it = node[0].begin();
  children.push_back(
      NodeManager::currentNM()->mkNode(kind::BITVECTOR_NOT, *child_it));
  for (++child_it; child_it != node[0].end(); ++child_it)
  {
    children.push_back(*child_it);
  }
  return utils::mkSortedNode(kind::BITVECTOR_XOR, children);
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<NotIdemp>(" << node << ")" << std::endl;
  TNode ret = node[0][0];
  while (ret.getKind() == kind::BITVECTOR_NOT
         && ret[0].getKind() == kind::BITVECTOR_NOT)
  {
    ret = ret[0][0];
  }
  return ret;
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<LtSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<LteSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroUlt
 *
 * 0 < a ==> a != 0
 */

template <>
inline bool RewriteRule<ZeroUlt>::applies(TNode node)
{
  return (node.getKind() == kind::BITVECTOR_ULT
          && node[0] == utils::mkZero(utils::getSize(node[0])));
}

template <>
inline Node RewriteRule<ZeroUlt>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<ZeroUlt>(" << node << ")" << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  return nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, node[0], node[1]));
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
  return (node.getKind() == kind::BITVECTOR_ULT
          && (utils::isZero(node[0]) || utils::isZero(node[1])));
}

template<> inline
Node RewriteRule<UltZero>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UltZero>(" << node << ")" << std::endl;
  if (utils::isZero(node[1]))
  {
    return utils::mkFalse();
  }
  return NodeManager::currentNM()->mkNode(
      kind::DISTINCT, utils::mkZero(utils::getSize(node[0])), node[1]);
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
  return (node.getKind() == kind::BITVECTOR_ULT && utils::isOne(node[1]));
}

template <>
inline Node RewriteRule<UltOne>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UltOne>(" << node << ")" << std::endl;
  return NodeManager::currentNM()->mkNode(
      kind::EQUAL, node[0], utils::mkZero(utils::getSize(node[0])));
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
  return node.getKind() == kind::BITVECTOR_ULT
         && (utils::isOnes(node[0]) || utils::isOnes(node[1]));
}

template <>
inline Node RewriteRule<UltOnes>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UltOnes>(" << node << ")" << std::endl;
  if (utils::isOnes(node[1]))
  {
    return NodeManager::currentNM()->mkNode(
        kind::DISTINCT, node[0], utils::mkOnes(utils::getSize(node[1])));
  }
  return NodeManager::currentNM()->mkConst(false);
}

/* -------------------------------------------------------------------------- */

/**
 * 
 */
template<> inline
bool RewriteRule<SltZero>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLT &&
          node[1] == utils::mkZero(utils::getSize(node[0])));
}

template <>
inline Node RewriteRule<SltZero>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SltZero>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node[0]);
  Node most_significant_bit = utils::mkExtract(node[0], size - 1, size - 1);
  return NodeManager::currentNM()->mkNode(
      kind::EQUAL, most_significant_bit, utils::mkOne(1));
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<UltSelf>(" << node << ")" << std::endl;
  return utils::mkFalse(); 
}


/* -------------------------------------------------------------------------- */

/**
 * UleZero
 *
 * a <= 0 ==> a = 0
 */

template<> inline
bool RewriteRule<UleZero>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[1] == utils::mkZero(utils::getSize(node[0])));
}

template <>
inline Node RewriteRule<UleZero>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UleZero>(" << node << ")" << std::endl;
  return NodeManager::currentNM()->mkNode(kind::EQUAL, node[0], node[1]);
}

/* -------------------------------------------------------------------------- */

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
  Trace("bv-rewrite") << "RewriteRule<UleSelf>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/* -------------------------------------------------------------------------- */

/**
 * ZeroUle
 *
 * 0 <= a ==> true
 */

template<> inline
bool RewriteRule<ZeroUle>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          node[0] == utils::mkZero(utils::getSize(node[0])));
}

template<> inline
Node RewriteRule<ZeroUle>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<ZeroUle>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/* -------------------------------------------------------------------------- */

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
  return (node.getKind() == kind::BITVECTOR_ULE
          && node[1] == utils::mkOnes(size));
}

template<> inline
Node RewriteRule<UleMax>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UleMax>(" << node << ")" << std::endl;
  return utils::mkTrue(); 
}

/* -------------------------------------------------------------------------- */

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

template <>
inline Node RewriteRule<NotUlt>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NotUlt>(" << node << ")" << std::endl;
  Node ult = node[0];
  Node a = ult[0];
  Node b = ult[1];
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULE, b, a);
}

/* -------------------------------------------------------------------------- */

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

template <>
inline Node RewriteRule<NotUle>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NotUle>(" << node << ")" << std::endl;
  Node ult = node[0];
  Node a = ult[0];
  Node b = ult[1];
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULT, b, a);
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
  if (node.getKind() != kind::BITVECTOR_MULT)
    return false;

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
  NodeManager *nm = NodeManager::currentNM();
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
    return utils::mkZero(size);
  }

  Node a;
  if (children.empty())
  {
    a = utils::mkOne(size);
  }
  else
  {
    a = utils::mkNaryNode(kind::BITVECTOR_MULT, children);
  }

  if (isNeg && size > 1)
  {
    a = nm->mkNode(kind::BITVECTOR_NEG, a);
  }
  if (exponent == 0)
  {
    return a;
  }
  Node extract = utils::mkExtract(a, size - exponent - 1, 0);
  Node zeros = utils::mkConst(exponent, 0);
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
  if (node.getKind() != kind::BITVECTOR_EXTRACT)
    return false;
  unsigned low = utils::getExtractLow(node);
  node = node[0];

  if (node.getKind() != kind::BITVECTOR_MULT ||
      node.getNumChildren() != 2 ||
      utils::getSize(node) <= 64)
    return false;

  if (node[0].getKind() != kind::BITVECTOR_CONCAT ||
      node[1].getKind() != kind::BITVECTOR_CONCAT ||
      !node[0][0].isConst() ||
      !node[1][0].isConst())
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

  // NodeManager *nm = NodeManager::currentNM();
  // Node new_mult = nm->mkNode(kind::BITVECTOR_MULT, extract1, extract2);
  // Node result = utils::mkExtract(nm->mkNode(kind::BITVECTOR_CONCAT, k_zeroes, new_mult), high, low);

  // since the extract is over multiplier bits that have to be 0, return 0
  Node result = utils::mkConst(bitwidth, 0u); 
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
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_NEG);
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
  if (node.getKind() == kind::BITVECTOR_UDIV
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
  NodeManager *nm = NodeManager::currentNM();
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
    Node zeros = utils::mkConst(power, 0);

    ret = nm->mkNode(kind::BITVECTOR_CONCAT, zeros, extract);
  }
  if (isNeg && size > 1)
  {
    ret = nm->mkNode(kind::BITVECTOR_NEG, ret);
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
  return (node.getKind() == kind::BITVECTOR_UDIV
          && node[1] == utils::mkConst(utils::getSize(node), 0));
}

template <>
inline Node RewriteRule<UdivZero>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UdivZero>(" << node << ")" << std::endl;
  return utils::mkOnes(utils::getSize(node));
}

/* -------------------------------------------------------------------------- */

/**
 * UdivOne
 *
 * (a udiv 1) ==> a
 */

template <>
inline bool RewriteRule<UdivOne>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UDIV
          && node[1] == utils::mkConst(utils::getSize(node), 1));
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
  if (node.getKind() == kind::BITVECTOR_UREM
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
  TNode a = node[0];
  bool isNeg = false;
  unsigned power = utils::isPow2Const(node[1], isNeg) - 1;
  Node ret;
  if (power == 0)
  {
    ret = utils::mkZero(utils::getSize(node));
  }
  else
  {
    Node extract = utils::mkExtract(a, power - 1, 0);
    Node zeros = utils::mkZero(utils::getSize(node) - power);
    ret = NodeManager::currentNM()->mkNode(
        kind::BITVECTOR_CONCAT, zeros, extract);
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
  return (node.getKind() == kind::BITVECTOR_UREM
          && node[1] == utils::mkConst(utils::getSize(node), 1));
}

template<> inline
Node RewriteRule<UremOne>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UremOne>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/* -------------------------------------------------------------------------- */

/**
 * UremSelf 
 *
 * (a urem a) ==> 0
 */

template<> inline
bool RewriteRule<UremSelf>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_UREM && node[0] == node[1]);
}

template<> inline
Node RewriteRule<UremSelf>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<UremSelf>(" << node << ")" << std::endl;
  return utils::mkConst(utils::getSize(node), 0); 
}

/* -------------------------------------------------------------------------- */

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
  return (node.getKind() == kind::BITVECTOR_UGT
          && node[0].getKind() == kind::BITVECTOR_UREM
          && node[0][1] == node[1]);
}

template <>
inline Node RewriteRule<UgtUrem>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UgtUrem>(" << node << ")" << std::endl;
  const Node& T = node[0][0];
  const Node& x = node[1];
  Node zero = utils::mkConst(utils::getSize(x), 0);
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(kind::AND,
                    nm->mkNode(kind::EQUAL, x, zero),
                    nm->mkNode(kind::BITVECTOR_UGT, T, zero));
}

/* -------------------------------------------------------------------------- */

/**
 * BBAddNeg
 *
 * -a1 - a2 - ... - an + ak + ..  ==> - (a1 + a2 + ... + an) + ak
 *
 */

template <>
inline bool RewriteRule<BBAddNeg>::applies(TNode node)
{
  if (node.getKind() != kind::BITVECTOR_ADD)
  {
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

template <>
inline Node RewriteRule<BBAddNeg>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BBAddNeg>(" << node << ")" << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  std::vector<Node> children;
  unsigned neg_count = 0;
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    if (node[i].getKind() == kind::BITVECTOR_NEG)
    {
      ++neg_count;
      children.push_back(nm->mkNode(kind::BITVECTOR_NOT, node[i][0]));
    }
    else
    {
      children.push_back(node[i]);
    }
  }
  Assert(neg_count != 0);
  children.push_back(utils::mkConst(utils::getSize(node), neg_count));

  return utils::mkNaryNode(kind::BITVECTOR_ADD, children);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<MergeSignExtend>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_SIGN_EXTEND ||
      (node[0].getKind() != kind::BITVECTOR_SIGN_EXTEND &&
       node[0].getKind() != kind::BITVECTOR_ZERO_EXTEND))
    return false;
  return true;
}

template<> inline
Node RewriteRule<MergeSignExtend>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<MergeSignExtend>(" << node << ")" << std::endl;
  unsigned amount1 =
      node.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;

  NodeManager* nm = NodeManager::currentNM();
  if (node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND) {
    unsigned amount2 = node[0]
                           .getOperator()
                           .getConst<BitVectorZeroExtend>()
                           .d_zeroExtendAmount;
    if (amount2 == 0)
    {
      NodeBuilder nb(kind::BITVECTOR_SIGN_EXTEND);
      Node op = nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(amount1));
      nb << op << node[0][0];
      Node res = nb;
      return res;
    }
    NodeBuilder nb(kind::BITVECTOR_ZERO_EXTEND);
    Node op = nm->mkConst<BitVectorZeroExtend>(
        BitVectorZeroExtend(amount1 + amount2));
    nb << op << node[0][0];
    Node res = nb;
    return res;
  }
  Assert(node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND);
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
  return node.getKind() == kind::EQUAL &&
         ((node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND &&
           node[1].isConst()) ||
          (node[1].getKind() == kind::BITVECTOR_ZERO_EXTEND &&
           node[0].isConst()));
}

template <>
inline Node RewriteRule<ZeroExtendEqConst>::apply(TNode node) {
  TNode t, c;
  if (node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND) {
    t = node[0][0];
    c = node[1];
  } else {
    t = node[1][0];
    c = node[0];
  }
  BitVector c_hi =
      c.getConst<BitVector>().extract(utils::getSize(c) - 1, utils::getSize(t));
  BitVector c_lo = c.getConst<BitVector>().extract(utils::getSize(t) - 1, 0);
  BitVector zero = BitVector(c_hi.getSize(), Integer(0));

  if (c_hi == zero) {
    return NodeManager::currentNM()->mkNode(kind::EQUAL, t,
                                            utils::mkConst(c_lo));
  }
  return utils::mkFalse();
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
  return node.getKind() == kind::EQUAL &&
         ((node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND &&
           node[1].isConst()) ||
          (node[1].getKind() == kind::BITVECTOR_SIGN_EXTEND &&
           node[0].isConst()));
}

template <>
inline Node RewriteRule<SignExtendEqConst>::apply(TNode node) {
  TNode t, c;
  if (node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND) {
    t = node[0][0];
    c = node[1];
  } else {
    t = node[1][0];
    c = node[0];
  }
  unsigned pos_msb_t = utils::getSize(t) - 1;
  BitVector c_hi =
      c.getConst<BitVector>().extract(utils::getSize(c) - 1, pos_msb_t);
  BitVector c_lo = c.getConst<BitVector>().extract(pos_msb_t, 0);
  BitVector zero = BitVector(c_hi.getSize(), Integer(0));

  if (c_hi == zero || c_hi == ~zero) {
    return NodeManager::currentNM()->mkNode(kind::EQUAL, t,
                                            utils::mkConst(c_lo));
  }
  return utils::mkFalse();
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
  if (node.getKind() == kind::BITVECTOR_ULT &&
      ((node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND &&
        node[1].isConst()) ||
       (node[1].getKind() == kind::BITVECTOR_ZERO_EXTEND &&
        node[0].isConst()))) {
    TNode t, c;
    bool is_lhs = node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND;
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
  TNode t, c;
  bool is_lhs = node[0].getKind() == kind::BITVECTOR_ZERO_EXTEND;
  if (is_lhs) {
    t = node[0][0];
    c = node[1];
  } else {
    t = node[1][0];
    c = node[0];
  }
  Node c_lo =
      utils::mkConst(c.getConst<BitVector>().extract(utils::getSize(t) - 1, 0));

  if (is_lhs) {
    return NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULT, t, c_lo);
  }
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_ULT, c_lo, t);
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
  if (node.getKind() == kind::BITVECTOR_ULT
      && ((node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND
           && node[1].isConst())
          || (node[1].getKind() == kind::BITVECTOR_SIGN_EXTEND
              && node[0].isConst())))
  {
    TNode x, c;
    bool is_lhs = node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND;
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
  TNode x, c;
  bool is_lhs = node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND;
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
  Node c_lo = utils::mkConst(bv_c.extract(msb_x_pos, 0));
  // (1 << (n - 1)))
  BitVector bv_msb_x(size_c);
  bv_msb_x.setBit(msb_x_pos, true);
  // (~0 << (n - 1))
  BitVector bv_upper_bits =
      (~BitVector(size_c)).leftShift(BitVector(size_c, msb_x_pos));

  NodeManager* nm = NodeManager::currentNM();
  if (is_lhs)
  {
    // x[n-1:n-1] = 0
    if (bv_msb_x < bv_c && bv_c <= bv_upper_bits)
    {
      Node msb_x = utils::mkExtract(x, msb_x_pos, msb_x_pos);
      return nm->mkNode(kind::EQUAL, msb_x, utils::mkZero(1));
    }
    // x < c[n-1:0]
    Assert(bv_c <= bv_msb_x || bv_c >= bv_upper_bits);
    return nm->mkNode(kind::BITVECTOR_ULT, x, c_lo);
  }

  // x[n-1:n-1] = 1
  if (~bv_upper_bits <= bv_c && bv_c <= ~bv_msb_x)
  {
    Node msb_x = utils::mkExtract(x, msb_x_pos, msb_x_pos);
    return nm->mkNode(kind::EQUAL, msb_x, utils::mkOne(1));
  }
  // c[n-1:0] < x
  Assert(bv_c < bv_msb_x || bv_c >= ~bv_msb_x);
  return nm->mkNode(kind::BITVECTOR_ULT, c_lo, x);
}

/* -------------------------------------------------------------------------- */

/**
 */
template <>
inline bool RewriteRule<IneqElimConversion>::applies(TNode node)
{
  Kind k = node.getKind();
  if (k == kind::BITVECTOR_ULT || k == kind::BITVECTOR_ULE
      || k == kind::BITVECTOR_UGT || k == kind::BITVECTOR_UGE)
  {
    for (const Node& nc : node)
    {
      Kind nck = nc.getKind();
      if (nck != kind::INT_TO_BITVECTOR && nck != kind::CONST_BITVECTOR)
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
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> children;
  for (const Node& nc : node)
  {
    Kind nck = nc.getKind();
    if (nck == kind::INT_TO_BITVECTOR)
    {
      size_t bvSize = nc.getOperator().getConst<IntToBitVector>();
      Node w = nm->mkConstInt(Rational(Integer(2).pow(bvSize)));
      children.push_back(nm->mkNode(kind::INTS_MODULUS, nc[0], w));
    }
    else
    {
      Assert(nck == kind::CONST_BITVECTOR);
      children.push_back(nm->mkNode(kind::BITVECTOR_TO_NAT, nc));
    }
  }
  // E.g. (bvuge ((_ int2bv w) x) N) ---> (>= (mod x 2^w) (bv2nat N)).
  // Note that (bv2nat N) is subsequently rewritten to the appropriate integer
  // constant.
  Kind arithKind;
  switch (node.getKind())
  {
    case kind::BITVECTOR_ULT: arithKind = kind::LT; break;
    case kind::BITVECTOR_ULE: arithKind = kind::LEQ; break;
    case kind::BITVECTOR_UGT: arithKind = kind::GT; break;
    case kind::BITVECTOR_UGE: arithKind = kind::GEQ; break;
    default:
      Unhandled() << "Unknown kind for IneqElimConversion " << node;
      break;
  }
  return nm->mkNode(arithKind, children);
}

/* -------------------------------------------------------------------------- */

template<> inline
bool RewriteRule<MultSlice>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_MULT || node.getNumChildren() != 2) {
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
  NodeManager *nm = NodeManager::currentNM();
  unsigned bitwidth = utils::getSize(node[0]);
  Node zeros = utils::mkConst(bitwidth / 2, 0);
  TNode a = node[0];
  Node bottom_a = utils::mkExtract(a, bitwidth / 2 - 1, 0);
  Node top_a = utils::mkExtract(a, bitwidth - 1, bitwidth / 2);
  TNode b = node[1];
  Node bottom_b = utils::mkExtract(b, bitwidth / 2 - 1, 0);
  Node top_b = utils::mkExtract(b, bitwidth - 1, bitwidth / 2);

  Node term1 = nm->mkNode(kind::BITVECTOR_MULT,
                          nm->mkNode(kind::BITVECTOR_CONCAT, zeros, bottom_a),
                          nm->mkNode(kind::BITVECTOR_CONCAT, zeros, bottom_b));

  Node term2 = nm->mkNode(kind::BITVECTOR_CONCAT,
                          nm->mkNode(kind::BITVECTOR_MULT, top_b, bottom_a),
                          zeros);
  Node term3 = nm->mkNode(kind::BITVECTOR_CONCAT,
                          nm->mkNode(kind::BITVECTOR_MULT, top_a, bottom_b),
                          zeros);
  return nm->mkNode(kind::BITVECTOR_ADD, term1, term2, term3);
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
  if (node.getKind() != kind::BITVECTOR_ULT) return false;
  TNode x = node[0];
  TNode y1 = node[1];
  if (y1.getKind() != kind::BITVECTOR_ADD) return false;
  if (y1[0].getKind() != kind::CONST_BITVECTOR &&
      y1[1].getKind() != kind::CONST_BITVECTOR)
    return false;
  
  if (y1[0].getKind() == kind::CONST_BITVECTOR &&
      y1[1].getKind() == kind::CONST_BITVECTOR)
    return false;
  
  if (y1.getNumChildren() != 2)
    return false; 

  TNode one = y1[0].getKind() == kind::CONST_BITVECTOR ? y1[0] : y1[1];
  if (one != utils::mkConst(utils::getSize(one), 1)) return false;
  return true;
}

template <>
inline Node RewriteRule<UltAddOne>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<UltAddOne>(" << node << ")" << std::endl;
  NodeManager *nm = NodeManager::currentNM();
  TNode x = node[0];
  TNode y1 = node[1];
  TNode y = y1[0].getKind() != kind::CONST_BITVECTOR ? y1[0] : y1[1];
  unsigned size = utils::getSize(x);
  Node not_y_eq_1 =
      nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, y, utils::mkOnes(size)));
  Node not_y_lt_x =
      nm->mkNode(kind::NOT, nm->mkNode(kind::BITVECTOR_ULT, y, x));
  return nm->mkNode(kind::AND, not_y_eq_1, not_y_lt_x);
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
  TNode a = node[0];
  TNode b = node[1];
  for (unsigned i = 0; i < 2; ++i)
  {
    if (a.getKind() == kind::BITVECTOR_CONCAT
        && b.getKind() == kind::BITVECTOR_SIGN_EXTEND
        && a[0] == utils::mkZero(utils::getSize(a[0]))
        && utils::getSize(a[1]) <= utils::getSize(a[0])
        && utils::getSize(b[0]) <= utils::getSignExtendAmount(b))
    {
      return std::make_tuple(a[1], b[0], false);
    }
    else if (i == 0
             && a.getKind() == kind::BITVECTOR_SIGN_EXTEND
             && b.getKind() == kind::BITVECTOR_SIGN_EXTEND
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
  if (node.getKind() != kind::BITVECTOR_SLT
      || node[0].getKind() != kind::BITVECTOR_MULT
      || node[1].getKind() != kind::BITVECTOR_MULT)
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
  if (ml[0].getKind() == kind::BITVECTOR_ADD)
  {
    addxt = ml[0];
    a = ml[1];
  }
  else if (ml[1].getKind() == kind::BITVECTOR_ADD)
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
  bool is_sext;
  TNode ml[2], mr[2];

  std::tie(ml[0], ml[1], is_sext) = extract_ext_tuple(node[0]);
  std::tie(mr[0], mr[1], std::ignore) = extract_ext_tuple(node[1]);

  TNode addxt, x, t, a;
  if (ml[0].getKind() == kind::BITVECTOR_ADD)
  {
    addxt = ml[0];
    a = ml[1];
  }
  else
  {
    Assert(ml[1].getKind() == kind::BITVECTOR_ADD);
    addxt = ml[1];
    a = ml[0];
  }

  x = (mr[0] == a) ? mr[1] : mr[0];
  t = (addxt[0] == x) ? addxt[1] : addxt[0];

  NodeManager *nm = NodeManager::currentNM();
  Node zero_t = utils::mkZero(utils::getSize(t));
  Node zero_a = utils::mkZero(utils::getSize(a));

  NodeBuilder nb(kind::AND);
  Kind k = is_sext ? kind::BITVECTOR_SLT : kind::BITVECTOR_ULT;
  nb << t.eqNode(zero_t).notNode();
  nb << a.eqNode(zero_a).notNode();
  nb << nm->mkNode(k, addxt, x)
            .eqNode(nm->mkNode(kind::BITVECTOR_SGT, a, zero_a));
  return nb.constructNode();
}

/* -------------------------------------------------------------------------- */
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif
