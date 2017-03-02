/*********************                                                        */
/*! \file proof_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "cvc4_private.h"

#pragma once

#include <set>
#include <vector>
#include <sstream>
#include "expr/node_manager.h"

namespace CVC4 {

typedef __gnu_cxx::hash_set<Expr, ExprHashFunction> ExprSet;
typedef __gnu_cxx::hash_set<Node, NodeHashFunction> NodeSet;

typedef std::pair<Node, Node> NodePair;
typedef std::set<NodePair> NodePairSet;


class ProofLetCount {
public:
  static unsigned counter;
  static void resetCounter() { counter = 0; }
  static unsigned newId() { return ++counter; }

  unsigned count;
  unsigned id;
  ProofLetCount()
    : count(0)
    , id(-1)
  {}

  void increment() { ++count; }
  ProofLetCount(unsigned i)
    : count(1)
    , id(i)
  {}

  ProofLetCount(const ProofLetCount& other)
    : count(other.count)
    , id (other.id)
  {}

  bool operator==(const ProofLetCount &other) const {
    return other.id == id && other.count == count;
  }

  ProofLetCount& operator=(const ProofLetCount &rhs) {
    if (&rhs == this) return *this;
    id = rhs.id;
    count = rhs.count;
    return *this;
  }
};

struct LetOrderElement {
  Expr expr;
  unsigned id;
  LetOrderElement(Expr e, unsigned i)
    : expr(e)
    , id(i)
  {}

  LetOrderElement()
    : expr()
    , id(-1)
  {}
};

typedef std::vector<LetOrderElement> Bindings;

namespace utils {

std::string toLFSCKind(Kind kind);
std::string toLFSCKindTerm(Expr node);

inline unsigned getExtractHigh(Expr node) {
  return node.getOperator().getConst<BitVectorExtract>().high;
}

inline unsigned getExtractLow(Expr node) {
  return node.getOperator().getConst<BitVectorExtract>().low;
}

inline unsigned getSize(Type type) {
  BitVectorType bv(type);
  return bv.getSize();
}


inline unsigned getSize(Expr node) {
  Assert (node.getType().isBitVector());
  return getSize(node.getType());
}

inline Expr mkTrue() {
  return NodeManager::currentNM()->toExprManager()->mkConst<bool>(true);
}

inline Expr mkFalse() {
  return NodeManager::currentNM()->toExprManager()->mkConst<bool>(false);
}
inline BitVector mkBitVectorOnes(unsigned size) {
  Assert(size > 0);
  return BitVector(1, Integer(1)).signExtend(size - 1);
}

inline Expr mkExpr(Kind k , Expr expr) {
  return NodeManager::currentNM()->toExprManager()->mkExpr(k, expr);
}
inline Expr mkExpr(Kind k , Expr e1, Expr e2) {
  return NodeManager::currentNM()->toExprManager()->mkExpr(k, e1, e2);
}
inline Expr mkExpr(Kind k , std::vector<Expr>& children) {
  return NodeManager::currentNM()->toExprManager()->mkExpr(k, children);
}


inline Expr mkOnes(unsigned size) {
  BitVector val = mkBitVectorOnes(size);
  return NodeManager::currentNM()->toExprManager()->mkConst<BitVector>(val);
}

inline Expr mkConst(unsigned size, unsigned int value) {
  BitVector val(size, value);
  return NodeManager::currentNM()->toExprManager()->mkConst<BitVector>(val);
}

inline Expr mkConst(const BitVector& value) {
  return NodeManager::currentNM()->toExprManager()->mkConst<BitVector>(value);
}

inline Expr mkOr(const std::vector<Expr>& nodes) {
  std::set<Expr> all;
  all.insert(nodes.begin(), nodes.end());
  Assert(all.size() != 0 );

  if (all.size() == 1) {
    // All the same, or just one
    return nodes[0];
  }


  NodeBuilder<> disjunction(kind::OR);
  std::set<Expr>::const_iterator it = all.begin();
  std::set<Expr>::const_iterator it_end = all.end();
  while (it != it_end) {
    disjunction << Node::fromExpr(*it);
    ++ it;
  }

  Node res = disjunction;
  return res.toExpr();
}/* mkOr() */


inline Expr mkAnd(const std::vector<Expr>& conjunctions) {
  std::set<Expr> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 0) {
    return mkTrue();
  }

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }


  NodeBuilder<> conjunction(kind::AND);
  std::set<Expr>::const_iterator it = all.begin();
  std::set<Expr>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << Node::fromExpr(*it);
    ++ it;
  }

  Node res = conjunction;
  return res.toExpr();
}/* mkAnd() */

inline Expr mkSortedExpr(Kind kind, const std::vector<Expr>& children) {
  std::set<Expr> all;
  all.insert(children.begin(), children.end());

  if (all.size() == 0) {
    return mkTrue();
  }

  if (all.size() == 1) {
    // All the same, or just one
    return children[0];
  }


  NodeBuilder<> res(kind);
  std::set<Expr>::const_iterator it = all.begin();
  std::set<Expr>::const_iterator it_end = all.end();
  while (it != it_end) {
    res << Node::fromExpr(*it);
    ++ it;
  }

  return ((Node)res).toExpr();
}/* mkSortedNode() */

inline const bool getBit(Expr expr, unsigned i) {
  Assert (i < utils::getSize(expr) &&
          expr.isConst());
  Integer bit = expr.getConst<BitVector>().extract(i, i).getValue();
  return (bit == 1u);
}

void collectAtoms(TNode node, std::set<Node>& seen);


}
}
