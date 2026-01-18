/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Daniel Larraz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

bool getBit(TNode node, unsigned i)
{
  Assert(i < getSize(node) && node.getKind() == Kind::CONST_BITVECTOR);
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
  NodeManager* nm = node.getNodeManager();
  return node == mkOnes(nm, getSize(node));
}

bool isZero(TNode node)
{
  if (!node.isConst()) return false;
  NodeManager* nm = node.getNodeManager();
  return node == mkZero(nm, getSize(node));
}

bool isOne(TNode node)
{
  if (!node.isConst()) return false;
  NodeManager* nm = node.getNodeManager();
  return node == mkOne(nm, getSize(node));
}

unsigned isPow2Const(TNode node, bool& isNeg)
{
  if (node.getKind() != Kind::CONST_BITVECTOR)
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
  if (k == Kind::NOT)
  {
    node = node[0];
    k = node.getKind();
  }
  return k == Kind::EQUAL || k == Kind::BITVECTOR_ULT
         || k == Kind::BITVECTOR_SLT || k == Kind::BITVECTOR_UGT
         || k == Kind::BITVECTOR_UGE || k == Kind::BITVECTOR_SGT
         || k == Kind::BITVECTOR_SGE || k == Kind::BITVECTOR_ULE
         || k == Kind::BITVECTOR_SLE || k == Kind::BITVECTOR_REDOR
         || k == Kind::BITVECTOR_REDAND;
}

static bool isCoreEqTerm(bool iseq, TNode term, TNodeBoolMap& cache)
{
  TNode t = term.getKind() == Kind::NOT ? term[0] : term;

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
      Assert(k != Kind::CONST_BITVECTOR);
      if (k != Kind::EQUAL && (iseq || k != Kind::BITVECTOR_CONCAT)
          && (iseq || k != Kind::BITVECTOR_EXTRACT)
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
  TNode atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
  return atom.getKind() != Kind::EQUAL || atom[0].getType().isBitVector();
}

/* ------------------------------------------------------------------------- */

Node mkTrue(NodeManager* nm) { return nm->mkConst<bool>(true); }

Node mkFalse(NodeManager* nm) { return nm->mkConst<bool>(false); }

Node mkZero(NodeManager* nm, unsigned size)
{
  Assert(size > 0);
  return mkConst(nm, size, 0u);
}

Node mkOne(NodeManager* nm, unsigned size)
{
  Assert(size > 0);
  return mkConst(nm, size, 1u);
}

Node mkOnes(NodeManager* nm, unsigned size)
{
  Assert(size > 0);
  return mkConst(nm, BitVector::mkOnes(size));
}

Node mkMinSigned(NodeManager* nm, unsigned size)
{
  Assert(size > 0);
  return mkConst(nm, BitVector::mkMinSigned(size));
}

Node mkMaxSigned(NodeManager* nm, unsigned size)
{
  Assert(size > 0);
  return mkConst(nm, BitVector::mkMaxSigned(size));
}

/* ------------------------------------------------------------------------- */

Node mkConst(NodeManager* nm, unsigned size, unsigned int value)
{
  BitVector val(size, value);
  return nm->mkConst<BitVector>(val);
}

Node mkConst(NodeManager* nm, unsigned size, Integer& value)
{
  return nm->mkConst<BitVector>(BitVector(size, value));
}

Node mkConst(NodeManager* nm, const BitVector& value)
{
  return nm->mkConst<BitVector>(value);
}

/* ------------------------------------------------------------------------- */

Node mkVar(NodeManager* nm, unsigned size)
{
  return NodeManager::mkDummySkolem(
      "BVSKOLEM$$",
      nm->mkBitVectorType(size),
      "is a variable created by the theory of bitvectors");
}

/* ------------------------------------------------------------------------- */

Node mkSortedNode(Kind kind, TNode child1, TNode child2)
{
  Assert(kind == Kind::BITVECTOR_AND || kind == Kind::BITVECTOR_OR
         || kind == Kind::BITVECTOR_XOR);

  if (child1 < child2)
  {
    return NodeManager::mkNode(kind, child1, child2);
  }
  else
  {
    return NodeManager::mkNode(kind, child2, child1);
  }
}

Node mkSortedNode(Kind kind, std::vector<Node>& children)
{
  Assert(kind == Kind::BITVECTOR_AND || kind == Kind::BITVECTOR_OR
         || kind == Kind::BITVECTOR_XOR);
  Assert(children.size() > 0);
  if (children.size() == 1)
  {
    return children[0];
  }
  std::sort(children.begin(), children.end());
  return children[0].getNodeManager()->mkNode(kind, children);
}

/* ------------------------------------------------------------------------- */

Node mkNot(Node child) { return NodeManager::mkNode(Kind::NOT, child); }

Node mkAnd(TNode node1, TNode node2)
{
  return NodeManager::mkNode(Kind::AND, node1, node2);
}

Node mkOr(TNode node1, TNode node2)
{
  return NodeManager::mkNode(Kind::OR, node1, node2);
}

Node mkXor(TNode node1, TNode node2)
{
  return NodeManager::mkNode(Kind::XOR, node1, node2);
}

/* ------------------------------------------------------------------------- */

Node mkSignExtend(TNode node, unsigned amount)
{
  NodeManager* nm = node.getNodeManager();
  Node signExtendOp =
      nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(amount));
  return nm->mkNode(signExtendOp, node);
}

/* ------------------------------------------------------------------------- */

Node mkExtract(TNode node, unsigned high, unsigned low)
{
  NodeManager* nm = node.getNodeManager();
  Node extractOp = nm->mkConst<BitVectorExtract>(BitVectorExtract(high, low));
  return nm->mkNode(extractOp, node);
}

Node mkBit(TNode node, unsigned index)
{
  NodeManager* nm = node.getNodeManager();
  Node bitOp = nm->mkConst<BitVectorBit>(BitVectorBit(index));
  return nm->mkNode(bitOp, node);
}

/* ------------------------------------------------------------------------- */

Node mkConcat(TNode t1, TNode t2)
{
  return NodeManager::mkNode(Kind::BITVECTOR_CONCAT, t1, t2);
}

Node mkConcat(std::vector<Node>& children)
{
  if (children.size() > 1)
  {
    return children[0].getNodeManager()->mkNode(Kind::BITVECTOR_CONCAT,
                                                children);
  }
  return children[0];
}

Node mkConcat(TNode node, unsigned repeat)
{
  Assert(repeat);
  if (repeat == 1)
  {
    return node;
  }
  NodeBuilder result(node.getNodeManager(), Kind::BITVECTOR_CONCAT);
  for (unsigned i = 0; i < repeat; ++i)
  {
    result << node;
  }
  Node resultNode = result;
  return resultNode;
}

Node mkRepeat(TNode node, unsigned repeat)
{
  Assert(repeat);
  // This method does not incorporate optimizations,
  // e.g. automatically converting to concat or dropping repeat
  // of size one, since we use it to ensure that rewrites match
  // a particular form as defined in the RARE signatures.
  NodeManager* nm = node.getNodeManager();
  Node rop = nm->mkConst(BitVectorRepeat(repeat));
  return nm->mkNode(rop, node);
}

/* ------------------------------------------------------------------------- */

Node mkInc(TNode t)
{
  NodeManager* nm = t.getNodeManager();
  return NodeManager::mkNode(Kind::BITVECTOR_ADD, t, mkOne(nm, getSize(t)));
}

Node mkDec(TNode t)
{
  NodeManager* nm = t.getNodeManager();
  return NodeManager::mkNode(Kind::BITVECTOR_SUB, t, mkOne(nm, getSize(t)));
}

/* ------------------------------------------------------------------------- */

Node flattenAnd(std::vector<TNode>& queue)
{
  TNodeSet nodes;
  while (!queue.empty())
  {
    TNode current = queue.back();
    queue.pop_back();
    if (current.getKind() == Kind::AND)
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
