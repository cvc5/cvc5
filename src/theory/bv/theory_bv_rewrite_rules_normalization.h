/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Normalization rewrite rules of the BV theory.
 *
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_NORMALIZATION_H
#define CVC5__THEORY__BV__THEORY_BV_REWRITE_RULES_NORMALIZATION_H

#include <unordered_map>
#include <unordered_set>

#include "expr/node_algorithm.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * ExtractNot
 *
 *  (~ a) [i:j] ==> ~ (a[i:j])
 */
template<> inline
bool RewriteRule<ExtractNot>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_EXTRACT
          && node[0].getKind() == Kind::BITVECTOR_NOT);
}

template <>
inline Node RewriteRule<ExtractNot>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<ExtractNot>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  return NodeManager::mkNode(Kind::BITVECTOR_NOT, a);
}

/** 
 * ExtractSignExtend
 * 
 * (sign_extend k x) [i:j] => pushes extract in
 * 
 * @return 
 */

template<> inline
bool RewriteRule<ExtractSignExtend>::applies(TNode node) {
  if (node.getKind() == Kind::BITVECTOR_EXTRACT
      && node[0].getKind() == Kind::BITVECTOR_SIGN_EXTEND)
  {
    return true;
  }
  return false; 
}

template <>
inline Node RewriteRule<ExtractSignExtend>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<ExtractSignExtend>(" << node << ")"
                      << std::endl;
  TNode extendee = node[0][0];
  unsigned extendee_size = utils::getSize(extendee);

  unsigned high = utils::getExtractHigh(node);
  unsigned low = utils::getExtractLow(node);

  Node resultNode;
  // extract falls on extendee
  if (high < extendee_size)
  {
    resultNode = utils::mkExtract(extendee, high, low);
  }
  else if (low < extendee_size && high >= extendee_size)
  {
    // if extract overlaps sign extend and extendee
    Node low_extract = utils::mkExtract(extendee, extendee_size - 1, low);
    unsigned new_amount = high - extendee_size + 1;
    resultNode = utils::mkSignExtend(low_extract, new_amount);
  }
  else
  {
    // extract only over sign extend
    Assert(low >= extendee_size);
    unsigned top = utils::getSize(extendee) - 1;
    Node most_significant_bit = utils::mkExtract(extendee, top, top);
    std::vector<Node> bits;
    // use repeat, which enables RARE reconstruction to succeed
    resultNode = utils::mkRepeat(most_significant_bit, high - low + 1);
  }
  Trace("bv-rewrite") << "                           =>" << resultNode
                      << std::endl;
  return resultNode;
}

template<> inline
bool RewriteRule<FlattenAssocCommut>::applies(TNode node) {
  Kind kind = node.getKind();
  if (kind != Kind::BITVECTOR_ADD && kind != Kind::BITVECTOR_MULT
      && kind != Kind::BITVECTOR_OR && kind != Kind::BITVECTOR_XOR
      && kind != Kind::BITVECTOR_AND)
    return false;
  TNode::iterator child_it = node.begin();
  for(; child_it != node.end(); ++child_it) {
    if ((*child_it).getKind() == kind) {
      return true;
    }
  }
  return false;
}

template <>
inline Node RewriteRule<FlattenAssocCommut>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<FlattenAssocCommut>(" << node << ")"
                      << std::endl;
  std::vector<Node> processingStack;
  processingStack.push_back(node);
  std::vector<Node> children;
  Kind kind = node.getKind();

  while (!processingStack.empty())
  {
    TNode current = processingStack.back();
    processingStack.pop_back();

    // flatten expression
    if (current.getKind() == kind)
    {
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        processingStack.push_back(current[i]);
      }
    }
    else
    {
      children.push_back(current);
    }
  }
  if (node.getKind() == Kind::BITVECTOR_ADD
      || node.getKind() == Kind::BITVECTOR_MULT)
  {
    NodeManager* nm = node.getNodeManager();
    return utils::mkNaryNode(nm, kind, children);
  }
  else
  {
    return utils::mkSortedNode(kind, children);
  }
}

static inline void addToCoefMap(std::map<Node, BitVector>& map,
                                TNode term, const BitVector& coef) {
  if (map.find(term) != map.end()) {
    map[term] = map[term] + coef; 
  } else {
    map[term] = coef;
  }
}


static inline void updateCoefMap(TNode current, unsigned size,
                                 std::map<Node, BitVector>& factorToCoefficient,
                                 BitVector& constSum) {
  switch (current.getKind()) {
    case Kind::BITVECTOR_MULT:
    {
      // look for c * term, where c is a constant
      BitVector coeff;
      Node term;
      if (current.getNumChildren() == 2) {
        // Mult should be normalized with only one constant at end
        Assert(!current[0].isConst());
        if (current[1].isConst()) {
          coeff = current[1].getConst<BitVector>();
          term = current[0];
        }
      }
      else if (current[current.getNumChildren()-1].isConst()) {
        NodeBuilder nb(current.getNodeManager(), Kind::BITVECTOR_MULT);
        TNode::iterator child_it = current.begin();
        for(; (child_it+1) != current.end(); ++child_it) {
          Assert(!(*child_it).isConst());
          nb << (*child_it);
        }
        term = nb;
        coeff = (*child_it).getConst<BitVector>();
      }
      if (term.isNull()) {
        coeff = BitVector(size, (unsigned)1);
        term = current;
      }
      if (term.getKind() == Kind::BITVECTOR_SUB)
      {
        TNode a = term[0];
        TNode b = term[1];
        addToCoefMap(factorToCoefficient, a, coeff);
        addToCoefMap(factorToCoefficient, b, -coeff);
      }
      else if (term.getKind() == Kind::BITVECTOR_NEG)
      {
        addToCoefMap(factorToCoefficient, term[0], -BitVector(size, coeff));
      }
      else {
        addToCoefMap(factorToCoefficient, term, coeff);
      }
      break;
    }
    case Kind::BITVECTOR_SUB:
      // turn into a + (-1)*b
      Assert(current.getNumChildren() == 2);
      addToCoefMap(factorToCoefficient, current[0], BitVector(size, (unsigned)1)); 
      addToCoefMap(factorToCoefficient, current[1], -BitVector(size, (unsigned)1)); 
      break;
    case Kind::BITVECTOR_NEG:
      addToCoefMap(factorToCoefficient, current[0], -BitVector(size, (unsigned)1)); 
      break;
    case Kind::CONST_BITVECTOR:
    {
      BitVector constValue = current.getConst<BitVector>(); 
      constSum = constSum + constValue;
      break;
    }
    default:
      // store as 1 * current
      addToCoefMap(factorToCoefficient, current, BitVector(size, (unsigned)1)); 
      break;
  }
}

static inline void addToChildren(TNode term,
                                 unsigned size,
                                 BitVector coeff,
                                 std::vector<Node> &children)
{
  NodeManager* nm = term.getNodeManager();
  if (coeff == BitVector(size, (unsigned)0))
  {
    return;
  }
  else if (coeff == BitVector(size, (unsigned)1))
  {
    children.push_back(term);
  }
  else if (coeff == -BitVector(size, (unsigned)1))
  {
    // avoid introducing an extra multiplication
    children.push_back(nm->mkNode(Kind::BITVECTOR_NEG, term));
  }
  else if (term.getKind() == Kind::BITVECTOR_MULT)
  {
    NodeBuilder nb(nm, Kind::BITVECTOR_MULT);
    TNode::iterator child_it = term.begin();
    for (; child_it != term.end(); ++child_it)
    {
      nb << *child_it;
    }
    nb << utils::mkConst(nm, coeff);
    children.push_back(Node(nb));
  }
  else
  {
    Node coeffNode = utils::mkConst(nm, coeff);
    Node product = nm->mkNode(Kind::BITVECTOR_MULT, term, coeffNode);
    children.push_back(product);
  }
}

template <>
inline bool RewriteRule<AddCombineLikeTerms>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_ADD);
}

template <>
inline Node RewriteRule<AddCombineLikeTerms>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<AddCombineLikeTerms>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  unsigned size = utils::getSize(node);
  BitVector constSum(size, (unsigned)0);
  std::map<Node, BitVector> factorToCoefficient;

  // combine like-terms
  for (size_t i = 0, n = node.getNumChildren(); i < n; ++i)
  {
    TNode current = node[i];
    updateCoefMap(current, size, factorToCoefficient, constSum);
  }

  std::vector<Node> children;

  // construct result
  std::map<Node, BitVector>::const_iterator it = factorToCoefficient.begin();

  for (; it != factorToCoefficient.end(); ++it)
  {
    addToChildren(it->first, size, it->second, children);
  }

  if (constSum != BitVector(size, (unsigned)0))
  {
    children.push_back(utils::mkConst(nm, constSum));
  }

  size_t csize = children.size();
  if (csize == node.getNumChildren())
  {
    // If we couldn't combine any terms, we don't perform the rewrite. This is
    // important because we are otherwise reordering terms in the addition
    // based on the node ids of the terms that are multiplied with the
    // coefficients. Due to garbage collection we may see different id orders
    // for those nodes even when we perform one rewrite directly after the
    // other, so the rewrite wouldn't be idempotent.
    return node;
  }

  return csize == 0 ? utils::mkZero(nm, size)
                    : utils::mkNaryNode(nm, Kind::BITVECTOR_ADD, children);
}

template<> inline
bool RewriteRule<MultSimplify>::applies(TNode node) {
  return node.getKind() == Kind::BITVECTOR_MULT;
}

template <>
inline Node RewriteRule<MultSimplify>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<MultSimplify>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  unsigned size = utils::getSize(node);
  BitVector constant(size, Integer(1));

  bool isNeg = false;
  std::vector<Node> children;
  for (const TNode &current : node)
  {
    Node c = current;
    if (c.getKind() == Kind::BITVECTOR_NEG)
    {
      isNeg = !isNeg;
      c = c[0];
    }

    if (c.getKind() == Kind::CONST_BITVECTOR)
    {
      BitVector value = c.getConst<BitVector>();
      constant = constant * value;
      if (constant == BitVector(size, (unsigned)0))
      {
        return utils::mkConst(nm, size, 0);
      }
    }
    else
    {
      children.push_back(c);
    }
  }
  BitVector oValue = BitVector(size, static_cast<unsigned>(1));
  BitVector noValue = BitVector::mkOnes(size);

  if (children.empty())
  {
    return utils::mkConst(nm, isNeg ? -constant : constant);
  }

  std::sort(children.begin(), children.end());

  if (constant == noValue)
  {
    isNeg = !isNeg;
  }
  else if (constant != oValue)
  {
    if (isNeg)
    {
      isNeg = !isNeg;
      constant = -constant;
    }
    children.push_back(utils::mkConst(nm, constant));
  }

  Node ret = utils::mkNaryNode(nm, Kind::BITVECTOR_MULT, children);

  // if negative, negate entire node
  if (isNeg && size > 1)
  {
    ret = NodeManager::mkNode(Kind::BITVECTOR_NEG, ret);
  }
  return ret;
}

template<> inline
bool RewriteRule<MultDistribConst>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_MULT || node.getNumChildren() != 2)
  {
    return false;
  }
  Assert(!node[0].isConst());
  if (!node[1].isConst()) {
    return false;
  }
  TNode factor = node[0];
  return (factor.getKind() == Kind::BITVECTOR_ADD
          || factor.getKind() == Kind::BITVECTOR_SUB
          || factor.getKind() == Kind::BITVECTOR_NEG);
}

template <>
inline Node RewriteRule<MultDistribConst>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<MultDistribConst>(" << node << ")"
                      << std::endl;

  NodeManager* nm = node.getNodeManager();
  TNode constant = node[1];
  TNode factor = node[0];
  Assert(constant.getKind() == Kind::CONST_BITVECTOR);

  if (factor.getKind() == Kind::BITVECTOR_NEG)
  {
    // push negation on the constant part
    BitVector const_bv = constant.getConst<BitVector>();
    return NodeManager::mkNode(
        Kind::BITVECTOR_MULT, factor[0], utils::mkConst(nm, -const_bv));
  }

  std::vector<Node> children;
  for (unsigned i = 0; i < factor.getNumChildren(); ++i)
  {
    children.push_back(
        NodeManager::mkNode(Kind::BITVECTOR_MULT, factor[i], constant));
  }

  return utils::mkNaryNode(nm, factor.getKind(), children);
}

template<> inline
bool RewriteRule<MultDistrib>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_MULT || node.getNumChildren() != 2)
  {
    return false;
  }
  if (node[0].getKind() == Kind::BITVECTOR_ADD
      || node[0].getKind() == Kind::BITVECTOR_SUB)
  {
    return node[1].getKind() != Kind::BITVECTOR_ADD
           && node[1].getKind() != Kind::BITVECTOR_SUB;
  }
  return node[1].getKind() == Kind::BITVECTOR_ADD
         || node[1].getKind() == Kind::BITVECTOR_SUB;
}

template <>
inline Node RewriteRule<MultDistrib>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<MultDistrib>(" << node << ")"
                      << std::endl;

  bool is_rhs_factor = node[0].getKind() == Kind::BITVECTOR_ADD
                       || node[0].getKind() == Kind::BITVECTOR_SUB;
  TNode factor = !is_rhs_factor ? node[0] : node[1];
  TNode sum = is_rhs_factor ? node[0] : node[1];
  Assert(factor.getKind() != Kind::BITVECTOR_ADD
         && factor.getKind() != Kind::BITVECTOR_SUB
         && (sum.getKind() == Kind::BITVECTOR_ADD
             || sum.getKind() == Kind::BITVECTOR_SUB));

  std::vector<Node> children;
  for (unsigned i = 0; i < sum.getNumChildren(); ++i)
  {
    children.push_back(
        NodeManager::mkNode(Kind::BITVECTOR_MULT, sum[i], factor));
  }

  NodeManager* nm = node.getNodeManager();
  return utils::mkNaryNode(nm, sum.getKind(), children);
}

template <>
inline bool RewriteRule<SolveEq>::applies(TNode node)
{
  if (node.getKind() != Kind::EQUAL
      || (node[0].isVar() && !expr::hasSubterm(node[1], node[0]))
      || (node[1].isVar() && !expr::hasSubterm(node[0], node[1])))
  {
    return false;
  }
  return true;
}

// Doesn't do full solving (yet), instead, if a term appears both on lhs and
// rhs, it subtracts from both sides so that one side's coeff is zero
template <>
inline Node RewriteRule<SolveEq>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<SolveEq>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();

  TNode left = node[0];
  TNode right = node[1];

  unsigned size = utils::getSize(left);
  BitVector zero(size, (unsigned)0);
  BitVector leftConst(size, (unsigned)0);
  BitVector rightConst(size, (unsigned)0);
  std::map<Node, BitVector> leftMap, rightMap;

  // Collect terms and coefficients plus constant for left
  if (left.getKind() == Kind::BITVECTOR_ADD)
  {
    for (unsigned i = 0; i < left.getNumChildren(); ++i)
    {
      updateCoefMap(left[i], size, leftMap, leftConst);
    }
  }
  else if (left.getKind() == Kind::BITVECTOR_NOT && left[0] == right)
  {
    return utils::mkFalse(nm);
  }
  else
  {
    updateCoefMap(left, size, leftMap, leftConst);
  }

  // Collect terms and coefficients plus constant for right
  if (right.getKind() == Kind::BITVECTOR_ADD)
  {
    for (unsigned i = 0; i < right.getNumChildren(); ++i)
    {
      updateCoefMap(right[i], size, rightMap, rightConst);
    }
  }
  else if (right.getKind() == Kind::BITVECTOR_NOT && right[0] == left)
  {
    return utils::mkFalse(nm);
  }
  else
  {
    updateCoefMap(right, size, rightMap, rightConst);
  }

  std::vector<Node> childrenLeft, childrenRight;

  std::map<Node, BitVector>::const_iterator iLeft = leftMap.begin(),
                                            iLeftEnd = leftMap.end();
  std::map<Node, BitVector>::const_iterator iRight = rightMap.begin(),
                                            iRightEnd = rightMap.end();

  BitVector coeffLeft;
  TNode termLeft;
  if (iLeft != iLeftEnd)
  {
    coeffLeft = iLeft->second;
    termLeft = iLeft->first;
  }

  BitVector coeffRight;
  TNode termRight;
  if (iRight != iRightEnd)
  {
    coeffRight = iRight->second;
    termRight = iRight->first;
  }

  // Changed tracks whether there have been any changes to the coefficients or
  // constants of the left- or right-hand side. We perform a rewrite only if
  // that is the case. This is important because we are otherwise reordering
  // terms in the addition based on the node ids of the terms that are
  // multiplied with the coefficients. Due to garbage collection we may see
  // different id orders for those nodes even when we perform one rewrite
  // directly after the other, so the rewrite wouldn't be idempotent.
  bool changed = false;
  bool incLeft, incRight;

  while (iLeft != iLeftEnd || iRight != iRightEnd)
  {
    incLeft = incRight = false;
    if (iLeft != iLeftEnd && (iRight == iRightEnd || termLeft < termRight))
    {
      addToChildren(termLeft, size, coeffLeft, childrenLeft);
      incLeft = true;
    }
    else if (iLeft == iLeftEnd || termRight < termLeft)
    {
      Assert(iRight != iRightEnd);
      addToChildren(termRight, size, coeffRight, childrenRight);
      incRight = true;
    }
    else
    {
      if (coeffLeft > coeffRight)
      {
        addToChildren(termLeft, size, coeffLeft - coeffRight, childrenLeft);
      }
      else if (coeffRight > coeffLeft)
      {
        addToChildren(termRight, size, coeffRight - coeffLeft, childrenRight);
      }
      incLeft = incRight = true;
      changed = true;
    }
    if (incLeft)
    {
      ++iLeft;
      if (iLeft != iLeftEnd)
      {
        Assert(termLeft < iLeft->first);
        coeffLeft = iLeft->second;
        termLeft = iLeft->first;
      }
    }
    if (incRight)
    {
      ++iRight;
      if (iRight != iRightEnd)
      {
        Assert(termRight < iRight->first);
        coeffRight = iRight->second;
        termRight = iRight->first;
      }
    }
  }

  // construct result

  // If both constants are nonzero, combine on right, otherwise leave them where
  // they are
  if (rightConst != zero)
  {
    changed |= (leftConst != zero);
    rightConst = rightConst - leftConst;
    leftConst = zero;
    if (rightConst != zero)
    {
      childrenRight.push_back(utils::mkConst(nm, rightConst));
    }
  }
  else if (leftConst != zero)
  {
    childrenLeft.push_back(utils::mkConst(nm, leftConst));
  }

  Node newLeft, newRight;

  if (childrenRight.size() == 0 && leftConst != zero)
  {
    Assert(childrenLeft.back().isConst()
           && childrenLeft.back().getConst<BitVector>() == leftConst);
    if (childrenLeft.size() == 1)
    {
      // c = 0 ==> false
      return utils::mkFalse(nm);
    }
    // special case - if right is empty and left has a constant, move the
    // constant
    childrenRight.push_back(utils::mkConst(nm, -leftConst));
    childrenLeft.pop_back();
    changed = true;
  }

  if (childrenLeft.size() == 0)
  {
    if (rightConst != zero)
    {
      Assert(childrenRight.back().isConst()
             && childrenRight.back().getConst<BitVector>() == rightConst);
      if (childrenRight.size() == 1)
      {
        // 0 = c ==> false
        return utils::mkFalse(nm);
      }
      // special case - if left is empty and right has a constant, move the
      // constant
      newLeft = utils::mkConst(nm, -rightConst);
      childrenRight.pop_back();
      changed = true;
    }
    else
    {
      newLeft = utils::mkConst(nm, size, (unsigned)0);
    }
  }
  else
  {
    newLeft = utils::mkNaryNode(nm, Kind::BITVECTOR_ADD, childrenLeft);
  }

  if (childrenRight.size() == 0)
  {
    newRight = utils::mkConst(nm, size, (unsigned)0);
  }
  else
  {
    newRight = utils::mkNaryNode(nm, Kind::BITVECTOR_ADD, childrenRight);
  }

  if (!changed)
  {
    return node;
  }

  if (newLeft == newRight)
  {
    Assert(newLeft == utils::mkConst(nm, size, (unsigned)0));
    return utils::mkTrue(nm);
  }

  if (newLeft < newRight)
  {
    return newRight.eqNode(newLeft);
  }

  return newLeft.eqNode(newRight);
}

template<> inline
bool RewriteRule<BitwiseEq>::applies(TNode node) {
  if (node.getKind() != Kind::EQUAL || utils::getSize(node[0]) != 1)
  {
    return false;
  }
  TNode term;
  BitVector c;
  if (node[0].getKind() == Kind::CONST_BITVECTOR)
  {
    c = node[0].getConst<BitVector>();
    term = node[1];
  }
  else if (node[1].getKind() == Kind::CONST_BITVECTOR)
  {
    c = node[1].getConst<BitVector>();
    term = node[0];
  }
  else {
    return false;
  }
  switch (term.getKind()) {
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR:
      //operator BITVECTOR_XOR 2: "bitwise xor"
    case Kind::BITVECTOR_NOT:
    case Kind::BITVECTOR_NAND:
    case Kind::BITVECTOR_NOR:
      //operator BITVECTOR_XNOR 2 "bitwise xnor"
    case Kind::BITVECTOR_COMP:
    case Kind::BITVECTOR_NEG: return true; break;
    default:
      break;
  }
  return false;
}


static inline Node mkNodeKind(Kind k, TNode node, TNode c) {
  unsigned i = 0;
  unsigned nc = node.getNumChildren();
  NodeBuilder nb(node.getNodeManager(), k);
  for(; i < nc; ++i) {
    nb << node[i].eqNode(c);
  }
  return nb;
}


template<> inline
Node RewriteRule<BitwiseEq>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<BitwiseEq>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();

  TNode term;
  BitVector c;

  if (node[0].getKind() == Kind::CONST_BITVECTOR)
  {
    c = node[0].getConst<BitVector>();
    term = node[1];
  }
  else if (node[1].getKind() == Kind::CONST_BITVECTOR)
  {
    c = node[1].getConst<BitVector>();
    term = node[0];
  }

  bool eqOne = (c == BitVector(1,(unsigned)1));

  switch (term.getKind()) {
    case Kind::BITVECTOR_AND:
      if (eqOne) {
        return mkNodeKind(Kind::AND, term, utils::mkConst(nm, 1, (unsigned)1));
      }
      else {
        return mkNodeKind(Kind::OR, term, utils::mkConst(nm, 1, (unsigned)0));
      }
      break;
    case Kind::BITVECTOR_NAND:
      if (eqOne) {
        return mkNodeKind(Kind::OR, term, utils::mkConst(nm, 1, (unsigned)0));
      }
      else {
        return mkNodeKind(Kind::AND, term, utils::mkConst(nm, 1, (unsigned)1));
      }
      break;
    case Kind::BITVECTOR_OR:
      if (eqOne) {
        return mkNodeKind(Kind::OR, term, utils::mkConst(nm, 1, (unsigned)1));
      }
      else {
        return mkNodeKind(Kind::AND, term, utils::mkConst(nm, 1, (unsigned)0));
      }
      break;
    case Kind::BITVECTOR_NOR:
      if (eqOne) {
        return mkNodeKind(Kind::AND, term, utils::mkConst(nm, 1, (unsigned)0));
      }
      else {
        return mkNodeKind(Kind::OR, term, utils::mkConst(nm, 1, (unsigned)1));
      }
      break;
    case Kind::BITVECTOR_NOT: return term[0].eqNode(utils::mkConst(nm, ~c));
    case Kind::BITVECTOR_COMP:
      Assert(term.getNumChildren() == 2);
      if (eqOne) {
        return term[0].eqNode(term[1]);
      }
      else {
        return term[0].eqNode(term[1]).notNode();
      }
    case Kind::BITVECTOR_NEG: return term[0].eqNode(utils::mkConst(nm, c));
    default:
      break;
  }
  Unreachable();
}


/**
 * -(c * expr) ==> (-c * expr)
 * where c is a constant
 */
template<> inline
bool RewriteRule<NegMult>::applies(TNode node) {
  if (node.getKind() != Kind::BITVECTOR_NEG
      || node[0].getKind() != Kind::BITVECTOR_MULT)
  {
    return false;
  }
  return node[node.getNumChildren()-1].isConst();
}

template<> inline
Node RewriteRule<NegMult>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<NegMult>(" << node << ")" << std::endl;
  TNode mult = node[0];
  NodeBuilder nb(node.getNodeManager(), Kind::BITVECTOR_MULT);
  BitVector bv(utils::getSize(node), (unsigned)1);
  TNode::iterator child_it = mult.begin();
  for(; (child_it+1) != mult.end(); ++child_it) {
    nb << (*child_it);
  }
  Assert((*child_it).isConst());
  bv = (*child_it).getConst<BitVector>();
  nb << utils::mkConst(node.getNodeManager(), -bv);
  return Node(nb);
}

template<> inline
bool RewriteRule<NegSub>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_NEG
          && node[0].getKind() == Kind::BITVECTOR_SUB);
}

template <>
inline Node RewriteRule<NegSub>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NegSub>(" << node << ")" << std::endl;
  return NodeManager::mkNode(Kind::BITVECTOR_SUB, node[0][1], node[0][0]);
}

template <>
inline bool RewriteRule<NegAdd>::applies(TNode node)
{
  return (node.getKind() == Kind::BITVECTOR_NEG
          && node[0].getKind() == Kind::BITVECTOR_ADD);
}

template <>
inline Node RewriteRule<NegAdd>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<NegAdd>(" << node << ")" << std::endl;
  std::vector<Node> children;
  for (unsigned i = 0; i < node[0].getNumChildren(); ++i)
  {
    children.push_back(NodeManager::mkNode(Kind::BITVECTOR_NEG, node[0][i]));
  }
  NodeManager* nm = node.getNodeManager();
  return utils::mkNaryNode(nm, Kind::BITVECTOR_ADD, children);
}

struct Count {
  unsigned pos;
  unsigned neg;
  Count() : pos(0), neg(0) {}
  Count(unsigned p, unsigned n):
    pos(p),
    neg(n)
  {}
};

inline static void insert(std::unordered_map<TNode, Count>& map,
                          TNode node,
                          bool neg)
{
  if(map.find(node) == map.end()) {
    Count c = neg? Count(0,1) : Count(1, 0);
    map[node] = c; 
  } else {
    if (neg) {
      ++(map[node].neg);
    } else {
      ++(map[node].pos);
    }
  }
}

template<> inline
bool RewriteRule<AndSimplify>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_AND);
}

template <>
inline Node RewriteRule<AndSimplify>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<AndSimplify>(" << node << ")"
                      << std::endl;
  NodeManager* nm = node.getNodeManager();
  // this will remove duplicates
  std::unordered_map<TNode, Count> subterms;
  unsigned size = utils::getSize(node);
  BitVector constant = BitVector::mkOnes(size);
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    TNode current = node[i];
    // simplify constants
    if (current.getKind() == Kind::CONST_BITVECTOR)
    {
      BitVector bv = current.getConst<BitVector>();
      constant = constant & bv;
    }
    else
    {
      if (current.getKind() == Kind::BITVECTOR_NOT)
      {
        insert(subterms, current[0], true);
      }
      else
      {
        insert(subterms, current, false);
      }
    }
  }

  std::vector<Node> children;

  if (constant == BitVector(size, (unsigned)0))
  {
    return utils::mkZero(nm, size);
  }

  if (constant != BitVector::mkOnes(size))
  {
    children.push_back(utils::mkConst(nm, constant));
  }

  std::unordered_map<TNode, Count>::const_iterator it = subterms.begin();

  for (; it != subterms.end(); ++it)
  {
    if (it->second.pos > 0 && it->second.neg > 0)
    {
      // if we have a and ~a
      return utils::mkZero(nm, size);
    }
    else
    {
      // idempotence
      if (it->second.neg > 0)
      {
        // if it only occured negated
        children.push_back(NodeManager::mkNode(Kind::BITVECTOR_NOT, it->first));
      }
      else
      {
        // if it only occured positive
        children.push_back(it->first);
      }
    }
  }
  if (children.size() == 0)
  {
    return utils::mkOnes(nm, size);
  }

  return utils::mkSortedNode(Kind::BITVECTOR_AND, children);
}

template<> inline
bool RewriteRule<FlattenAssocCommutNoDuplicates>::applies(TNode node) {
  Kind kind = node.getKind();
  if (kind != Kind::BITVECTOR_OR && kind != Kind::BITVECTOR_AND) return false;
  TNode::iterator child_it = node.begin();
  for(; child_it != node.end(); ++child_it) {
    if ((*child_it).getKind() == kind) {
      return true;
    }
  }
  return false;
}
  
template<> inline
Node RewriteRule<FlattenAssocCommutNoDuplicates>::apply(TNode node) {
  Trace("bv-rewrite") << "RewriteRule<FlattenAssocCommut>(" << node << ")" << std::endl;
  std::vector<Node> processingStack;
  processingStack.push_back(node);
  std::unordered_set<TNode> processed;
  std::vector<Node> children;
  Kind kind = node.getKind(); 
  
  while (! processingStack.empty()) {
    TNode current = processingStack.back();
    processingStack.pop_back();
    if (processed.count(current))
      continue;

    processed.insert(current);
    
    // flatten expression
    if (current.getKind() == kind) {
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        processingStack.push_back(current[i]);
      }
    } else {
      children.push_back(current); 
    }
  }
  return utils::mkSortedNode(kind, children);
}
  
  
template<> inline
bool RewriteRule<OrSimplify>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_OR);
}

template <>
inline Node RewriteRule<OrSimplify>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<OrSimplify>(" << node << ")" << std::endl;
  NodeManager* nm = node.getNodeManager();
  // this will remove duplicates
  std::unordered_map<TNode, Count> subterms;
  unsigned size = utils::getSize(node);
  BitVector constant(size, (unsigned)0);

  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    TNode current = node[i];
    // simplify constants
    if (current.getKind() == Kind::CONST_BITVECTOR)
    {
      BitVector bv = current.getConst<BitVector>();
      constant = constant | bv;
    }
    else
    {
      if (current.getKind() == Kind::BITVECTOR_NOT)
      {
        insert(subterms, current[0], true);
      }
      else
      {
        insert(subterms, current, false);
      }
    }
  }

  std::vector<Node> children;

  if (constant == BitVector::mkOnes(size))
  {
    return utils::mkOnes(nm, size);
  }

  if (constant != BitVector(size, (unsigned)0))
  {
    children.push_back(utils::mkConst(nm, constant));
  }

  std::unordered_map<TNode, Count>::const_iterator it = subterms.begin();

  for (; it != subterms.end(); ++it)
  {
    if (it->second.pos > 0 && it->second.neg > 0)
    {
      // if we have a or ~a
      return utils::mkOnes(nm, size);
    }
    else
    {
      // idempotence
      if (it->second.neg > 0)
      {
        // if it only occured negated
        children.push_back(NodeManager::mkNode(Kind::BITVECTOR_NOT, it->first));
      }
      else
      {
        // if it only occured positive
        children.push_back(it->first);
      }
    }
  }

  if (children.size() == 0)
  {
    return utils::mkZero(nm, size);
  }
  return utils::mkSortedNode(Kind::BITVECTOR_OR, children);
}

template<> inline
bool RewriteRule<XorSimplify>::applies(TNode node) {
  return (node.getKind() == Kind::BITVECTOR_XOR);
}

template <>
inline Node RewriteRule<XorSimplify>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<XorSimplify>(" << node << ")"
                      << std::endl;

  NodeManager* nm = node.getNodeManager();

  std::unordered_map<TNode, Count> subterms;
  unsigned size = utils::getSize(node);
  BitVector constant;
  bool const_set = false;

  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    TNode current = node[i];
    // simplify constants
    if (current.getKind() == Kind::CONST_BITVECTOR)
    {
      BitVector bv = current.getConst<BitVector>();
      if (const_set)
      {
        constant = constant ^ bv;
      }
      else
      {
        const_set = true;
        constant = bv;
      }
    }
    else
    {
      // collect number of occurances of each term and its negation
      if (current.getKind() == Kind::BITVECTOR_NOT)
      {
        insert(subterms, current[0], true);
      }
      else
      {
        insert(subterms, current, false);
      }
    }
  }

  std::vector<Node> children;

  std::unordered_map<TNode, Count>::const_iterator it = subterms.begin();
  unsigned true_count = 0;
  for (; it != subterms.end(); ++it)
  {
    unsigned pos = it->second.pos;  // number of positive occurances
    unsigned neg = it->second.neg;  // number of negated occurances

    // remove duplicates using the following rules
    // a xor a ==> false
    // false xor false ==> false
    // check what did not reduce
    if (pos % 2 && neg % 2)
    {
      // we have a xor ~a ==> true
      ++true_count;
    }
    else if (pos % 2)
    {
      // we had a positive occurrence left
      children.push_back(it->first);
    }
    else if (neg % 2)
    {
      // we had a negative occurrence left
      children.push_back(NodeManager::mkNode(Kind::BITVECTOR_NOT, it->first));
    }
    // otherwise both reduced to false
  }

  std::vector<BitVector> xorConst;
  BitVector true_bv = BitVector::mkOnes(size);
  BitVector false_bv(size, (unsigned)0);

  if (true_count)
  {
    // true xor ... xor true ==> true (odd)
    //                       ==> false (even)
    xorConst.push_back(true_count % 2 ? true_bv : false_bv);
  }
  if (const_set)
  {
    xorConst.push_back(constant);
  }

  if (xorConst.size() > 0)
  {
    BitVector result = xorConst[0];
    for (unsigned i = 1; i < xorConst.size(); ++i)
    {
      result = result ^ xorConst[i];
    }
    children.push_back(utils::mkConst(nm, result));
  }
  if (children.empty())
  {
    return utils::mkConst(nm, false_bv);
  }

  return utils::mkSortedNode(Kind::BITVECTOR_XOR, children);
}

/** 
 * BitwiseSlicing
 * 
 * (a bvand c) ==> (concat (bvand a[i0:j0] c0) ... (bvand a[in:jn] cn))
 *  where c0,..., cn are maximally continuous substrings of 0 or 1 in the constant c 
 *
 * Note: this rule assumes AndSimplify has already been called on the node
 */
template<> inline
bool RewriteRule<BitwiseSlicing>::applies(TNode node) {
  if ((node.getKind() != Kind::BITVECTOR_AND
       && node.getKind() != Kind::BITVECTOR_OR
       && node.getKind() != Kind::BITVECTOR_XOR)
      || utils::getSize(node) == 1)
    return false; 
  // find the first constant and return true if it's not only 1..1 or only 0..0
  // (there could be more than one constant)
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i].getKind() == Kind::CONST_BITVECTOR)
    {
      BitVector constant = node[i].getConst<BitVector>();
      // we do not apply the rule if the constant is all 0s or all 1s
      if (constant == BitVector(utils::getSize(node), 0u)) return false;

      for (unsigned j = 0, csize = constant.getSize(); j < csize; ++j)
      {
        if (!constant.isBitSet(j)) return true;
      }
      return false;
    }
  }
  return false; 
}

template <>
inline Node RewriteRule<BitwiseSlicing>::apply(TNode node)
{
  Trace("bv-rewrite") << "RewriteRule<BitwiseSlicing>(" << node << ")"
                      << std::endl;
  // get the constant
  bool found_constant = false;
  TNode constant;
  std::vector<Node> other_children;
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    if (node[i].getKind() == Kind::CONST_BITVECTOR && !found_constant)
    {
      constant = node[i];
      found_constant = true;
    }
    else
    {
      other_children.push_back(node[i]);
    }
  }
  Assert(found_constant && other_children.size() == node.getNumChildren() - 1);

  NodeManager* nm = node.getNodeManager();
  Node other = utils::mkNaryNode(nm, node.getKind(), other_children);

  BitVector bv_constant = constant.getConst<BitVector>();
  std::vector<Node> concat_children;
  int start = bv_constant.getSize() - 1;
  int end = start;
  for (int i = end - 1; i >= 0; --i)
  {
    if (bv_constant.isBitSet(i + 1) != bv_constant.isBitSet(i))
    {
      Node other_extract = utils::mkExtract(other, end, start);
      Node const_extract = utils::mkExtract(constant, end, start);
      Node bitwise_op =
          NodeManager::mkNode(node.getKind(), const_extract, other_extract);
      concat_children.push_back(bitwise_op);
      start = end = i;
    }
    else
    {
      start--;
    }
    if (i == 0)
    {
      Node other_extract = utils::mkExtract(other, end, 0);
      Node const_extract = utils::mkExtract(constant, end, 0);
      Node bitwise_op =
          NodeManager::mkNode(node.getKind(), const_extract, other_extract);
      concat_children.push_back(bitwise_op);
    }
  }
  Node result = utils::mkConcat(concat_children);
  Trace("bv-rewrite") << "    =>" << result << std::endl;
  return result;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif
