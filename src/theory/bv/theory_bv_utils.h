/*********************                                                        */
/*! \file theory_bv_utils.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#pragma once 

#include <set>
#include <vector>
#include <sstream>
#include "expr/node_manager.h"

#ifdef CVC4_DEBUG
#define BVDebug(x) Debug(x)
#else
#define BVDebug(x) if (false) Debug(x)
#endif

namespace CVC4 {
namespace theory {
namespace bv {
namespace utils {

inline unsigned getExtractHigh(TNode node) {
  return node.getOperator().getConst<BitVectorExtract>().high;
}

inline unsigned getExtractLow(TNode node) {
  return node.getOperator().getConst<BitVectorExtract>().low;
}

inline unsigned getSize(TNode node) {
  return node.getType().getBitVectorSize();
}

inline Node mkTrue() {
  return NodeManager::currentNM()->mkConst<bool>(true);
}

inline Node mkFalse() {
  return NodeManager::currentNM()->mkConst<bool>(false);
}

inline Node mkAnd(std::vector<TNode>& children) {
  if (children.size() > 1) {
    return NodeManager::currentNM()->mkNode(kind::AND, children);
  } else {
    return children[0];
  }
}

inline Node mkAnd(std::vector<Node>& children) {
  return NodeManager::currentNM()->mkNode(kind::AND, children);
}

inline Node mkExtract(TNode node, unsigned high, unsigned low) {
  Node extractOp = NodeManager::currentNM()->mkConst<BitVectorExtract>(BitVectorExtract(high, low));
  std::vector<Node> children;
  children.push_back(node);
  return NodeManager::currentNM()->mkNode(extractOp, children);
}

inline Node mkConcat(std::vector<Node>& children) {
  if (children.size() > 1)
    return NodeManager::currentNM()->mkNode(kind::BITVECTOR_CONCAT, children);
  else
    return children[0];
}

inline Node mkConcat(TNode t1, TNode t2) {
    return NodeManager::currentNM()->mkNode(kind::BITVECTOR_CONCAT, t1, t2);
}


inline Node mkConst(const BitVector& value) {
  return NodeManager::currentNM()->mkConst<BitVector>(value);
}

inline void getConjuncts(TNode node, std::set<TNode>& conjuncts) {
  if (node.getKind() != kind::AND) {
    conjuncts.insert(node);
  } else {
    for (unsigned i = 0; i < node.getNumChildren(); ++ i) {
      getConjuncts(node[i], conjuncts);
    }
  }
}

inline void getConjuncts(std::vector<TNode>& nodes, std::set<TNode>& conjuncts) {
  for (unsigned i = 0, i_end = nodes.size(); i < i_end; ++ i) {
    getConjuncts(nodes[i], conjuncts);
  }
}

inline Node mkConjunction(const std::set<TNode> nodes) {
  std::set<TNode> expandedNodes;

  std::set<TNode>::const_iterator it = nodes.begin();
  std::set<TNode>::const_iterator it_end = nodes.end();
  while (it != it_end) {
    TNode current = *it;
    if (current != mkTrue()) {
      Assert(current.getKind() == kind::EQUAL || (current.getKind() == kind::NOT && current[0].getKind() == kind::EQUAL));
      expandedNodes.insert(current);
    }
    ++ it;
  }

  Assert(expandedNodes.size() > 0);
  if (expandedNodes.size() == 1) {
    return *expandedNodes.begin();
  }

  NodeBuilder<> conjunction(kind::AND);

  it = expandedNodes.begin();
  it_end = expandedNodes.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}

// Turn a set into a string
inline std::string setToString(const std::set<TNode>& nodeSet) {
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

// Turn a vector into a string
inline std::string vectorToString(const std::vector<Node>& nodes) {
  std::stringstream out;
  out << "[";
  for (unsigned i = 0; i < nodes.size(); ++ i) {
    if (i > 0) {
      out << ",";
    }
    out << nodes[i];
  }
  out << "]";
  return out.str();
}

}
}
}
}
