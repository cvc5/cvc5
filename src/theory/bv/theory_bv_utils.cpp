/*********************                                                        */
/*! \file theory_bv_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Liana Hadarean, Tim King
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

uint32_t pow2(uint32_t n)
{
  Assert(n < 32);
  uint32_t one = 1;
  return one << n;
}

/* ------------------------------------------------------------------------- */

BitVector mkBitVectorOnes(unsigned size)
{
  Assert(size > 0);
  return BitVector(1, Integer(1)).signExtend(size - 1);
}

BitVector mkBitVectorMinSigned(unsigned size)
{
  Assert(size > 0);
  return BitVector(size).setBit(size - 1);
}

BitVector mkBitVectorMaxSigned(unsigned size)
{
  Assert(size > 0);
  return ~mkBitVectorMinSigned(size);
}

/* ------------------------------------------------------------------------- */

unsigned getSize(TNode node)
{
  return node.getType().getBitVectorSize();
}

const bool getBit(TNode node, unsigned i)
{
  Assert(i < utils::getSize(node) && node.getKind() == kind::CONST_BITVECTOR);
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
  return node == utils::mkConst(utils::getSize(node), 0u);
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

bool isBVGroundTerm(TNode node)
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
  if (node.getKind() == kind::EQUAL || node.getKind() == kind::BITVECTOR_ULT
      || node.getKind() == kind::BITVECTOR_SLT
      || node.getKind() == kind::BITVECTOR_UGT
      || node.getKind() == kind::BITVECTOR_UGE
      || node.getKind() == kind::BITVECTOR_SGT
      || node.getKind() == kind::BITVECTOR_SGE
      || node.getKind() == kind::BITVECTOR_ULE
      || node.getKind() == kind::BITVECTOR_SLE
      || node.getKind() == kind::BITVECTOR_REDOR
      || node.getKind() == kind::BITVECTOR_REDAND
      || (node.getKind() == kind::NOT
          && (node[0].getKind() == kind::EQUAL
              || node[0].getKind() == kind::BITVECTOR_ULT
              || node[0].getKind() == kind::BITVECTOR_SLT
              || node[0].getKind() == kind::BITVECTOR_UGT
              || node[0].getKind() == kind::BITVECTOR_UGE
              || node[0].getKind() == kind::BITVECTOR_SGT
              || node[0].getKind() == kind::BITVECTOR_SGE
              || node[0].getKind() == kind::BITVECTOR_ULE
              || node[0].getKind() == kind::BITVECTOR_SLE
              || node[0].getKind() == kind::BITVECTOR_REDOR
              || node[0].getKind() == kind::BITVECTOR_REDAND)))
  {
    return true;
  }
  else
  {
    return false;
  }
}

bool isCoreTerm(TNode term, TNodeBoolMap& cache)
{
  term = term.getKind() == kind::NOT ? term[0] : term;
  TNodeBoolMap::const_iterator it = cache.find(term);
  if (it != cache.end())
  {
    return it->second;
  }

  if (term.getNumChildren() == 0) return true;

  if (theory::Theory::theoryOf(theory::THEORY_OF_TERM_BASED, term) == THEORY_BV)
  {
    Kind k = term.getKind();
    if (k != kind::CONST_BITVECTOR && k != kind::BITVECTOR_CONCAT
        && k != kind::BITVECTOR_EXTRACT && k != kind::EQUAL
        && term.getMetaKind() != kind::metakind::VARIABLE)
    {
      cache[term] = false;
      return false;
    }
  }

  for (unsigned i = 0; i < term.getNumChildren(); ++i)
  {
    if (!isCoreTerm(term[i], cache))
    {
      cache[term] = false;
      return false;
    }
  }

  cache[term] = true;
  return true;
}

bool isEqualityTerm(TNode term, TNodeBoolMap& cache)
{
  term = term.getKind() == kind::NOT ? term[0] : term;
  TNodeBoolMap::const_iterator it = cache.find(term);
  if (it != cache.end())
  {
    return it->second;
  }

  if (term.getNumChildren() == 0) return true;

  if (theory::Theory::theoryOf(theory::THEORY_OF_TERM_BASED, term) == THEORY_BV)
  {
    Kind k = term.getKind();
    if (k != kind::CONST_BITVECTOR && k != kind::EQUAL
        && term.getMetaKind() != kind::metakind::VARIABLE)
    {
      cache[term] = false;
      return false;
    }
  }

  for (unsigned i = 0; i < term.getNumChildren(); ++i)
  {
    if (!isEqualityTerm(term[i], cache))
    {
      cache[term] = false;
      return false;
    }
  }

  cache[term] = true;
  return true;
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

Node mkOnes(unsigned size)
{
  BitVector val = mkBitVectorOnes(size);
  return NodeManager::currentNM()->mkConst<BitVector>(val);
}

Node mkZero(unsigned size)
{
  return mkConst(size, 0u);
}

Node mkOne(unsigned size)
{
  return mkConst(size, 1u);
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

Node mkNode(Kind kind, TNode child)
{
  return NodeManager::currentNM()->mkNode(kind, child);
}

Node mkNode(Kind kind, TNode child1, TNode child2)
{
  return NodeManager::currentNM()->mkNode(kind, child1, child2);
}

Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3)
{
  return NodeManager::currentNM()->mkNode(kind, child1, child2, child3);
}

Node mkNode(Kind kind, std::vector<Node>& children)
{
  Assert(children.size() > 0);
  if (children.size() == 1)
  {
    return children[0];
  }
  return NodeManager::currentNM()->mkNode(kind, children);
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

Node mkAnd(const std::vector<TNode>& conjunctions)
{
  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 0)
  {
    return mkTrue();
  }

  if (all.size() == 1)
  {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end)
  {
    conjunction << *it;
    ++it;
  }

  return conjunction;
}

Node mkAnd(const std::vector<Node>& conjunctions)
{
  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 0)
  {
    return mkTrue();
  }

  if (all.size() == 1)
  {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end)
  {
    conjunction << *it;
    ++it;
  }

  return conjunction;
}

Node mkOr(TNode node1, TNode node2)
{
  return NodeManager::currentNM()->mkNode(kind::OR, node1, node2);
}

Node mkOr(const std::vector<Node>& nodes)
{
  std::set<TNode> all;
  all.insert(nodes.begin(), nodes.end());

  if (all.size() == 0)
  {
    return mkTrue();
  }

  if (all.size() == 1)
  {
    // All the same, or just one
    return nodes[0];
  }

  NodeBuilder<> disjunction(kind::OR);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end)
  {
    disjunction << *it;
    ++it;
  }

  return disjunction;
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
  Node extractOp = NodeManager::currentNM()->mkConst<BitVectorExtract>(
      BitVectorExtract(high, low));
  std::vector<Node> children;
  children.push_back(node);
  return NodeManager::currentNM()->mkNode(extractOp, children);
}

Node mkBitOf(TNode node, unsigned index)
{
  Node bitOfOp =
      NodeManager::currentNM()->mkConst<BitVectorBitOf>(BitVectorBitOf(index));
  return NodeManager::currentNM()->mkNode(bitOfOp, node);
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
      kind::BITVECTOR_PLUS, t, bv::utils::mkOne(bv::utils::getSize(t)));
}

Node mkDec(TNode t)
{
  return NodeManager::currentNM()->mkNode(
      kind::BITVECTOR_SUB, t, bv::utils::mkOne(bv::utils::getSize(t)));
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

Node mkConjunction(const std::set<TNode> nodes)
{
  std::set<TNode> expandedNodes;

  std::set<TNode>::const_iterator it = nodes.begin();
  std::set<TNode>::const_iterator it_end = nodes.end();
  while (it != it_end)
  {
    TNode current = *it;
    if (current != mkTrue())
    {
      Assert(current.getKind() == kind::EQUAL
             || (current.getKind() == kind::NOT
                 && current[0].getKind() == kind::EQUAL));
      expandedNodes.insert(current);
    }
    ++it;
  }

  Assert(expandedNodes.size() > 0);
  if (expandedNodes.size() == 1)
  {
    return *expandedNodes.begin();
  }

  NodeBuilder<> conjunction(kind::AND);

  it = expandedNodes.begin();
  it_end = expandedNodes.end();
  while (it != it_end)
  {
    conjunction << *it;
    ++it;
  }

  return conjunction;
}

Node mkConjunction(const std::vector<TNode>& nodes)
{
  std::vector<TNode> expandedNodes;

  std::vector<TNode>::const_iterator it = nodes.begin();
  std::vector<TNode>::const_iterator it_end = nodes.end();
  while (it != it_end)
  {
    TNode current = *it;

    if (current != mkTrue())
    {
      Assert(isBVPredicate(current));
      expandedNodes.push_back(current);
    }
    ++it;
  }

  if (expandedNodes.size() == 0)
  {
    return mkTrue();
  }

  if (expandedNodes.size() == 1)
  {
    return *expandedNodes.begin();
  }

  NodeBuilder<> conjunction(kind::AND);

  it = expandedNodes.begin();
  it_end = expandedNodes.end();
  while (it != it_end)
  {
    conjunction << *it;
    ++it;
  }

  return conjunction;
}

/* ------------------------------------------------------------------------- */

void getConjuncts(TNode node, std::set<TNode>& conjuncts)
{
  if (node.getKind() != kind::AND)
  {
    conjuncts.insert(node);
  }
  else
  {
    for (unsigned i = 0; i < node.getNumChildren(); ++i)
    {
      getConjuncts(node[i], conjuncts);
    }
  }
}

void getConjuncts(std::vector<TNode>& nodes, std::set<TNode>& conjuncts)
{
  for (unsigned i = 0, i_end = nodes.size(); i < i_end; ++i)
  {
    getConjuncts(nodes[i], conjuncts);
  }
}

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

std::string setToString(const std::set<TNode>& nodeSet) {
  std::stringstream out;
  out << "[";
  std::set<TNode>::const_iterator it = nodeSet.begin();
  std::set<TNode>::const_iterator it_end = nodeSet.end();
  bool first = true;
  while (it != it_end) {
    if (!first) {
      out << ",";
    }
    first = false;
    out << *it;
    ++ it;
  }
  out << "]";
  return out.str();
}

std::string vectorToString(const std::vector<Node>& nodes)
{
  std::stringstream out;
  out << "[";
  for (unsigned i = 0; i < nodes.size(); ++i)
  {
    if (i > 0)
    {
      out << ",";
    }
    out << nodes[i];
  }
  out << "]";
  return out.str();
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

uint64_t numNodes(TNode node, NodeSet& seen)
{
  if (seen.find(node) != seen.end()) return 0;

  uint64_t size = 1;
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    size += numNodes(node[i], seen);
  }
  seen.insert(node);
  return size;
}

/* ------------------------------------------------------------------------- */

void collectVariables(TNode node, NodeSet& vars)
{
  if (vars.find(node) != vars.end()) return;

  if (Theory::isLeafOf(node, THEORY_BV)
      && node.getKind() != kind::CONST_BITVECTOR)
  {
    vars.insert(node);
    return;
  }
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    collectVariables(node[i], vars);
  }
}

/* ------------------------------------------------------------------------- */

}/* CVC4::theory::bv::utils namespace */
}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
