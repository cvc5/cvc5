/*********************                                                        */
/*! \file theory_bv_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv_utils.h"

#include <vector>

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace bv {
namespace utils {

Node mkSum(std::vector<Node>& children, unsigned width)
{
  std::size_t nchildren = children.size();

  if (nchildren == 0)
  {
    return mkZero(width);
  }
  else if (nchildren == 1)
  {
    return children[0];
  }
  return NodeManager::currentNM()->mkNode(kind::BITVECTOR_PLUS, children);
}

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

bool isCoreTerm(TNode term, TNodeBoolMap& cache) {
  term = term.getKind() == kind::NOT ? term[0] : term;
  TNodeBoolMap::const_iterator it = cache.find(term);
  if (it != cache.end()) {
    return it->second;
  }

  if (term.getNumChildren() == 0)
    return true;

  if (theory::Theory::theoryOf(theory::THEORY_OF_TERM_BASED, term) == THEORY_BV) {
    Kind k = term.getKind();
    if (k != kind::CONST_BITVECTOR &&
        k != kind::BITVECTOR_CONCAT &&
        k != kind::BITVECTOR_EXTRACT &&
        k != kind::EQUAL &&
        term.getMetaKind() != kind::metakind::VARIABLE) {
      cache[term] = false;
      return false;
    }
  }

  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    if (!isCoreTerm(term[i], cache)) {
      cache[term] = false;
      return false;
    }
  }

  cache[term]= true;
  return true;
}

bool isEqualityTerm(TNode term, TNodeBoolMap& cache) {
  term = term.getKind() == kind::NOT ? term[0] : term;
  TNodeBoolMap::const_iterator it = cache.find(term);
  if (it != cache.end()) {
    return it->second;
  }

  if (term.getNumChildren() == 0)
    return true;

  if (theory::Theory::theoryOf(theory::THEORY_OF_TERM_BASED, term) == THEORY_BV) {
    Kind k = term.getKind();
    if (k != kind::CONST_BITVECTOR &&
        k != kind::EQUAL &&
        term.getMetaKind() != kind::metakind::VARIABLE) {
      cache[term] = false;
      return false;
    }
  }

  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    if (!isEqualityTerm(term[i], cache)) {
      cache[term] = false;
      return false;
    }
  }

  cache[term]= true;
  return true;
}


uint64_t numNodes(TNode node, NodeSet& seen) {
  if (seen.find(node) != seen.end())
    return 0;

  uint64_t size = 1;
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    size += numNodes(node[i], seen);
  }
  seen.insert(node);
  return size;
}

void collectVariables(TNode node, NodeSet& vars) {
  if (vars.find(node) != vars.end())
    return;

  if (Theory::isLeafOf(node, THEORY_BV) && node.getKind() != kind::CONST_BITVECTOR) {
    vars.insert(node);
    return;
  }
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectVariables(node[i], vars);
  }
}

}/* CVC4::theory::bv::utils namespace */
}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
