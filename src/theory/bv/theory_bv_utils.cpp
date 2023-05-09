/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory BV.
 */

#include "theory/bv/theory_bv_utils.h"

#include <vector>

#include "expr/skolem_manager.h"
#include "options/theory_options.h"
#include "theory/theory.h"
#include "util/bitvector.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
  return node.getConst<BitVector>().extract(i, i).getValue() == 1u;
}

/* ------------------------------------------------------------------------- */

unsigned getExtractHigh(TNode node)
{
  return node.getOperator().getConst<BitVectorExtract>().d_high;
}

unsigned getExtractLow(TNode node)
{
  return node.getOperator().getConst<BitVectorExtract>().d_low;
}

unsigned getSignExtendAmount(TNode node)
{
  return node.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;
}

/* ------------------------------------------------------------------------- */

bool isOnes(TNode node)
{
  if (!node.isConst()) return false;
  return node == mkOnes(getSize(node));
}

bool isZero(TNode node)
{
  if (!node.isConst()) return false;
  return node == mkZero(getSize(node));
}

bool isOne(TNode node)
{
  if (!node.isConst()) return false;
  return node == mkOne(getSize(node));
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

  for (const TNode& n : node)
  {
    if (!n.isConst()) { return false; }
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
  std::unordered_map<TNode, bool> visited;
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

    if (theory::Theory::theoryOf(n, options::TheoryOfMode::THEORY_OF_TERM_BASED)
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
  SkolemManager* sm = nm->getSkolemManager();
  return sm->mkDummySkolem("BVSKOLEM$$",
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
  NodeBuilder result(kind::BITVECTOR_CONCAT);
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
      kind::BITVECTOR_ADD, t, mkOne(getSize(t)));
}

Node mkDec(TNode t)
{
  return NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_SUB, t, mkOne(getSize(t)));
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
      for (const TNode& n : current)
      {
        if (nodes.count(n) == 0) { queue.push_back(n); }
      }
    }
    else
    {
      nodes.insert(current);
    }
  }
  std::vector<TNode> children(nodes.begin(), nodes.end());
  return mkAnd(children);
}

}  // namespace utils
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
