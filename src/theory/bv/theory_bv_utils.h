/*********************                                                        */
/*! \file theory_bv_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Dejan Jovanovic, Tim King
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

#include "cvc4_private.h"

#pragma once

#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node_manager.h"

namespace CVC4 {
namespace theory {
namespace bv {

typedef std::unordered_set<Node, NodeHashFunction> NodeSet;
typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;

namespace utils {

typedef std::unordered_map<TNode, bool, TNodeHashFunction> TNodeBoolMap;
typedef std::unordered_set<Node, NodeHashFunction> NodeSet;

/* Get the bit-width of given node. */
unsigned getSize(TNode node);

/* Get bit at given index. */
const bool getBit(TNode node, unsigned i);

/* Get the upper index of given extract node. */
unsigned getExtractHigh(TNode node);
/* Get the lower index of given extract node. */
unsigned getExtractLow(TNode node);

/* Get the number of bits by which a given node is extended. */
unsigned getSignExtendAmount(TNode node);

/* Returns true if given node represents a zero bit-vector.  */
bool isZero(TNode node);
/* If node is a constant of the form 2^c or -2^c, then this function returns
 * c+1. Otherwise, this function returns 0. The flag isNeg is updated to
 * indicate whether node is negative.  */
unsigned isPow2Const(TNode node, bool& isNeg);
/* Returns true if node or all of its children is const. */
bool isBvConstTerm(TNode node);
/* Returns true if node is a predicate over bit-vector nodes. */
bool isBVPredicate(TNode node);
/* Returns true if given term is a THEORY_BV \Sigma_core term.
 * \Sigma_core = { concat, extract, =, bv constants, bv variables } */
bool isCoreTerm(TNode term, TNodeBoolMap& cache);
/* Returns true if given term is a THEORY_BV \Sigma_equality term.
 * \Sigma_equality = { =, bv constants, bv variables }  */
bool isEqualityTerm(TNode term, TNodeBoolMap& cache);
/* Returns true if given node is an atom that is bit-blasted.  */
bool isBitblastAtom(Node lit);

/* Create Boolean node representing true. */
Node mkTrue();
/* Create Boolean node representing false. */
Node mkFalse();
/* Create bit-vector node representing a bit-vector of ones of given size. */
Node mkOnes(unsigned size);
/* Create bit-vector node representing a zero bit-vector of given size. */
Node mkZero(unsigned size);
/* Create bit-vector node representing a bit-vector value one of given size. */
Node mkOne(unsigned size);
/* Create bit-vector node representing the min signed value of given size. */
Node mkMinSigned(unsigned size);
/* Create bit-vector node representing the max signed value of given size. */
Node mkMaxSigned(unsigned size);

/* Create bit-vector constant of given size and value. */
Node mkConst(unsigned size, unsigned int value);
Node mkConst(unsigned size, Integer& value);
/* Create bit-vector constant from given bit-vector. */
Node mkConst(const BitVector& value);

/* Create bit-vector variable. */
Node mkVar(unsigned size);

/* Create n-ary bit-vector node of kind BITVECTOR_AND, BITVECTOR_OR or
 * BITVECTOR_XOR where its children are sorted  */
Node mkSortedNode(Kind kind, TNode child1, TNode child2);
Node mkSortedNode(Kind kind, std::vector<Node>& children);

/* Create n-ary node of associative/commutative kind.  */
template<bool ref_count>
Node mkNaryNode(Kind k, const std::vector<NodeTemplate<ref_count>>& nodes)
{
  Assert (k == kind::AND
          || k == kind::OR
          || k == kind::XOR
          || k == kind::BITVECTOR_AND
          || k == kind::BITVECTOR_OR
          || k == kind::BITVECTOR_XOR
          || k == kind::BITVECTOR_PLUS
          || k == kind::BITVECTOR_SUB
          || k == kind::BITVECTOR_MULT);

  if (nodes.size() == 1) { return nodes[0]; }
  return NodeManager::currentNM()->mkNode(k, nodes);
}

/* Create node of kind NOT. */
Node mkNot(Node child);
/* Create node of kind AND. */
Node mkAnd(TNode node1, TNode node2);
/* Create n-ary node of kind AND. */
template<bool ref_count>
Node mkAnd(const std::vector<NodeTemplate<ref_count>>& conjunctions)
{
  std::set<TNode> all(conjunctions.begin(), conjunctions.end());
  Assert(all.size() > 0);

  /* All the same, or just one  */
  if (all.size() == 1) { return conjunctions[0]; }

  NodeBuilder<> conjunction(kind::AND);
  for (const Node& n : all) { conjunction << n; }
  return conjunction;
}

/* ------------------------------------------------------------------------- */

/* Create node of kind OR. */
Node mkOr(TNode node1, TNode node2);
/* Create n-ary node of kind OR.  */
template<bool ref_count>
Node mkOr(const std::vector<NodeTemplate<ref_count>>& nodes)
{
  std::set<TNode> all(nodes.begin(), nodes.end());
  Assert(all.size() > 0);

  /* All the same, or just one  */
  if (all.size() == 1) { return nodes[0]; }

  NodeBuilder<> disjunction(kind::OR);
  for (const Node& n : all) { disjunction << n; }
  return disjunction;
}
/* Create node of kind XOR. */
Node mkXor(TNode node1, TNode node2);

/* Create signed extension node where given node is extended by given amount. */
Node mkSignExtend(TNode node, unsigned amount);

/* Create extract node where bits from index high to index low are extracted
 * from given node. */
Node mkExtract(TNode node, unsigned high, unsigned low);
/* Create extract node of bit-width 1 where the resulting node represents
 * the bit at given index.  */
Node mkBitOf(TNode node, unsigned index);

/* Create n-ary concat node of given children.  */
Node mkConcat(TNode t1, TNode t2);
Node mkConcat(std::vector<Node>& children);
/* Create concat by repeating given node n times.
 * Returns given node if n = 1. */
Node mkConcat(TNode node, unsigned repeat);

/* Create bit-vector addition node representing the increment of given node. */
Node mkInc(TNode t);
/* Create bit-vector addition node representing the decrement of given node. */
Node mkDec(TNode t);

/* Unsigned multiplication overflow detection.
 * See M.Gok, M.J. Schulte, P.I. Balzola, "Efficient integer multiplication
 * overflow detection circuits", 2001.
 * http://ieeexplore.ieee.org/document/987767 */
Node mkUmulo(TNode t1, TNode t2);

/* Create conjunction.  */
Node mkConjunction(const std::vector<TNode>& nodes);

/* Create a flattened and node.  */
Node flattenAnd(std::vector<TNode>& queue);

/* Create the intersection of two vectors of uint32_t. */
void intersect(const std::vector<uint32_t>& v1,
               const std::vector<uint32_t>& v2,
               std::vector<uint32_t>& intersection);

}
}
}
}
