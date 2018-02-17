/*********************                                                        */
/*! \file theory_bv_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Util functions for theory BV.
 **
 ** Util functions for theory BV.
 **/

#include "theory/bv/theory_bv_utils.h"

#include <vector>

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace bv {
namespace utils {

/* ------------------------------------------------------------------------- */

unsigned getSize(TNode node)
{
  return node.getType().getBitVectorSize();
}

const bool getBit(TNode node, unsigned i)
{
  Assert(i < getSize(node) && node.getKind() == kind::CONST_BITVECTOR);
  Integer bit = node.getConst<BitVector>().extract(i, i).getValue();
  return (bit == 1u);
}

/* ------------------------------------------------------------------------- */

unsigned getExtractHigh(TNode node)
{
  return node.getOperator().getConst<BitVectorExtract>().high;
}

unsigned getExtractLow(TNode node)
{
  return node.getOperator().getConst<BitVectorExtract>().low;
}

unsigned getSignExtendAmount(TNode node)
{
  return node.getOperator().getConst<BitVectorSignExtend>().signExtendAmount;
}

/* ------------------------------------------------------------------------- */

bool isZero(TNode node)
{
  if (!node.isConst()) return false;
  return node == mkZero(getSize(node));
}

unsigned isPow2Const(TNode node, bool& isNeg)
{
  if (node.getKind() != kind::CONST_BITVECTOR)
  {
    return false;
  }

  BitVector bv = node.getConst<BitVector>();
  unsigned p = bv.isPow2();
  if (p != 0)
  {
    isNeg = false;
    return p;
  }
  BitVector nbv = -bv;
  p = nbv.isPow2();
  if (p != 0)
  {
    isNeg = true;
    return p;
  }
  return false;
}

bool isBvConstTerm(TNode node)
{
  if (node.getNumChildren() == 0)
  {
    return node.isConst();
  }

  for (size_t i = 0; i < node.getNumChildren(); ++i)
  {
    if (!node[i].isConst())
    {
      return false;
    }
  }
  return true;
}

bool isBVPredicate(TNode node)
{
  Kind k = node.getKind();
  if (k == kind::NOT)
  {
    node = node[0];
    k = node.getKind();
  }
  return k == kind::EQUAL
         || k == kind::BITVECTOR_ULT
         || k == kind::BITVECTOR_SLT
         || k == kind::BITVECTOR_UGT
         || k == kind::BITVECTOR_UGE
         || k == kind::BITVECTOR_SGT
         || k == kind::BITVECTOR_SGE
         || k == kind::BITVECTOR_ULE
         || k == kind::BITVECTOR_SLE
         || k == kind::BITVECTOR_REDOR
         || k == kind::BITVECTOR_REDAND;
}

static bool isCoreEqTerm(bool iseq, TNode term, TNodeBoolMap& cache)
{
  TNode t = term.getKind() == kind::NOT ? term[0] : term;

  std::vector<TNode> stack;
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  stack.push_back(t);

  while (!stack.empty())
  {
    TNode n = stack.back();
    stack.pop_back();

    if (cache.find(n) != cache.end()) continue;

    if (n.getNumChildren() == 0)
    {
      cache[n] = true;
      visited[n] = true;
      continue;
    }

    if (theory::Theory::theoryOf(theory::THEORY_OF_TERM_BASED, n)
        == theory::THEORY_BV)
    {
      Kind k = n.getKind();
      Assert(k != kind::CONST_BITVECTOR);
      if (k != kind::EQUAL
          && (iseq || k != kind::BITVECTOR_CONCAT)
          && (iseq || k != kind::BITVECTOR_EXTRACT)
          && n.getMetaKind() != kind::metakind::VARIABLE)
      {
        cache[n] = false;
        continue;
      }
    }

    if (!visited[n])
    {
      visited[n] = true;
      stack.push_back(n);
      stack.insert(stack.end(), n.begin(), n.end());
    }
    else
    {
      bool iseqt = true;
      for (const Node& c : n)
      {
        Assert(cache.find(c) != cache.end());
        if (!cache[c])
        {
          iseqt = false;
          break;
        }
      }
      cache[n] = iseqt;
    }
  }
  Assert(cache.find(t) != cache.end());
  return cache[t];
}

bool isCoreTerm(TNode term, TNodeBoolMap& cache)
{
  return isCoreEqTerm(false, term, cache);
}

bool isEqualityTerm(TNode term, TNodeBoolMap& cache)
{
  return isCoreEqTerm(true, term, cache);
}

bool isBitblastAtom(Node lit)
{
  TNode atom = lit.getKind() == kind::NOT ? lit[0] : lit;
  return atom.getKind() != kind::EQUAL || atom[0].getType().isBitVector();
}

/* ------------------------------------------------------------------------- */

Node mkTrue()
{
  return NodeManager::currentNM()->mkConst<bool>(true);
}

Node mkFalse()
{
  return NodeManager::currentNM()->mkConst<bool>(false);
}

Node mkZero(unsigned size)
{
  Assert(size > 0);
  return mkConst(size, 0u);
}

Node mkOne(unsigned size)
{
  Assert(size > 0);
  return mkConst(size, 1u);
}

Node mkOnes(unsigned size)
{
  Assert(size > 0);
  return mkConst(BitVector::mkOnes(size));
}

Node mkMinSigned(unsigned size)
{
  Assert(size > 0);
  return mkConst(BitVector::mkMinSigned(size));
}

Node mkMaxSigned(unsigned size)
{
  Assert(size > 0);
  return mkConst(BitVector::mkMaxSigned(size));
}

/* ------------------------------------------------------------------------- */

Node mkConst(unsigned size, unsigned int value)
{
  BitVector val(size, value);
  return NodeManager::currentNM()->mkConst<BitVector>(val);
}

Node mkConst(unsigned size, Integer& value)
{
  return NodeManager::currentNM()->mkConst<BitVector>(BitVector(size, value));
}

Node mkConst(const BitVector& value)
{
  return NodeManager::currentNM()->mkConst<BitVector>(value);
}

/* ------------------------------------------------------------------------- */

Node mkVar(unsigned size)
{
  NodeManager* nm = NodeManager::currentNM();

  return nm->mkSkolem("BVSKOLEM$$",
                      nm->mkBitVectorType(size),
                      "is a variable created by the theory of bitvectors");
}

/* ------------------------------------------------------------------------- */

Node mkSortedNode(Kind kind, TNode child1, TNode child2)
{
  Assert(kind == kind::BITVECTOR_AND || kind == kind::BITVECTOR_OR
         || kind == kind::BITVECTOR_XOR);

  if (child1 < child2)
  {
    return NodeManager::currentNM()->mkNode(kind, child1, child2);
  }
  else
  {
    return NodeManager::currentNM()->mkNode(kind, child2, child1);
  }
}

Node mkSortedNode(Kind kind, std::vector<Node>& children)
{
  Assert(kind == kind::BITVECTOR_AND || kind == kind::BITVECTOR_OR
         || kind == kind::BITVECTOR_XOR);
  Assert(children.size() > 0);
  if (children.size() == 1)
  {
    return children[0];
  }
  std::sort(children.begin(), children.end());
  return NodeManager::currentNM()->mkNode(kind, children);
}

/* ------------------------------------------------------------------------- */

Node mkNot(Node child)
{
  return NodeManager::currentNM()->mkNode(kind::NOT, child);
}

Node mkAnd(TNode node1, TNode node2)
{
  return NodeManager::currentNM()->mkNode(kind::AND, node1, node2);
}

Node mkOr(TNode node1, TNode node2)
{
  return NodeManager::currentNM()->mkNode(kind::OR, node1, node2);
}

Node mkXor(TNode node1, TNode node2)
{
  return NodeManager::currentNM()->mkNode(kind::XOR, node1, node2);
}

/* ------------------------------------------------------------------------- */

Node mkSignExtend(TNode node, unsigned amount)
{
  NodeManager* nm = NodeManager::currentNM();
  Node signExtendOp =
      nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(amount));
  return nm->mkNode(signExtendOp, node);
}

/* ------------------------------------------------------------------------- */

Node mkExtract(TNode node, unsigned high, unsigned low)
{
  NodeManager *nm = NodeManager::currentNM();
  Node extractOp = nm->mkConst<BitVectorExtract>(BitVectorExtract(high, low));
  return nm->mkNode(extractOp, node);
}

Node mkBitOf(TNode node, unsigned index)
{
  NodeManager *nm = NodeManager::currentNM();
  Node bitOfOp = nm->mkConst<BitVectorBitOf>(BitVectorBitOf(index));
  return nm->mkNode(bitOfOp, node);
}

/* ------------------------------------------------------------------------- */

Node mkConcat(TNode t1, TNode t2)
{
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_CONCAT, t1, t2);
}

Node mkConcat(std::vector<Node>& children)
{
  if (children.size() > 1)
    return NodeManager::currentNM()->mkNode(kind::BITVECTOR_CONCAT, children);
  else
    return children[0];
}

Node mkConcat(TNode node, unsigned repeat)
{
  Assert(repeat);
  if (repeat == 1)
  {
    return node;
  }
  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
  for (unsigned i = 0; i < repeat; ++i)
  {
    result << node;
  }
  Node resultNode = result;
  return resultNode;
}

/* ------------------------------------------------------------------------- */

Node mkInc(TNode t)
{
  return NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_PLUS, t, mkOne(getSize(t)));
}

Node mkDec(TNode t)
{
  return NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_SUB, t, mkOne(getSize(t)));
}

/* ------------------------------------------------------------------------- */

Node mkUmulo(TNode t1, TNode t2)
{
  unsigned w = getSize(t1);
  if (w == 1) return mkFalse();

  NodeManager* nm = NodeManager::currentNM();
  Node uppc;
  std::vector<Node> tmp;

  uppc = mkExtract(t1, w - 1, w - 1);
  for (size_t i = 1; i < w; ++i)
  {
    tmp.push_back(nm->mkNode(kind::BITVECTOR_AND, mkExtract(t2, i, i), uppc));
    uppc = nm->mkNode(
        kind::BITVECTOR_OR, mkExtract(t1, w - 1 - i, w - 1 - i), uppc);
  }
  Node zext_t1 = mkConcat(mkZero(1), t1);
  Node zext_t2 = mkConcat(mkZero(1), t2);
  Node mul = nm->mkNode(kind::BITVECTOR_MULT, zext_t1, zext_t2);
  tmp.push_back(mkExtract(mul, w, w));
  return nm->mkNode(kind::EQUAL, nm->mkNode(kind::BITVECTOR_OR, tmp), mkOne(1));
}

/* ------------------------------------------------------------------------- */

Node flattenAnd(std::vector<TNode>& queue)
{
  TNodeSet nodes;
  while (!queue.empty())
  {
    TNode current = queue.back();
    queue.pop_back();
    if (current.getKind() == kind::AND)
    {
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        if (nodes.count(current[i]) == 0)
        {
          queue.push_back(current[i]);
        }
      }
    }
    else
    {
      nodes.insert(current);
    }
  }
  std::vector<TNode> children;
  for (TNodeSet::const_iterator it = nodes.begin(); it != nodes.end(); ++it)
  {
    children.push_back(*it);
  }
  return mkAnd(children);
}

/* ------------------------------------------------------------------------- */

// FIXME: dumb code
void intersect(const std::vector<uint32_t>& v1,
                      const std::vector<uint32_t>& v2,
                      std::vector<uint32_t>& intersection) {
  for (unsigned i = 0; i < v1.size(); ++i) {
    bool found = false;
    for (unsigned j = 0; j < v2.size(); ++j) {
      if (v2[j] == v1[i]) {
        found = true;
        break;
      }
    }
    if (found) {
      intersection.push_back(v1[i]);
    }
  }
}

/* ------------------------------------------------------------------------- */

}/* CVC4::theory::bv::utils namespace */
}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
