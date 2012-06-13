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

#include "cvc4_private.h"

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

// this seems to behave strangely
inline const Integer& getBit(TNode node, unsigned i) {
  Assert (0); 
  Assert (node.getKind() == kind::CONST_BITVECTOR);
  return node.getConst<BitVector>().extract(i, i).getValue();
}

inline Node mkTrue() {
  return NodeManager::currentNM()->mkConst<bool>(true);
}

inline Node mkFalse() {
  return NodeManager::currentNM()->mkConst<bool>(false);
}

inline Node mkVar(unsigned size) {
  NodeManager* nm =  NodeManager::currentNM();
  return nm->mkVar(nm->mkBitVectorType(size)); 
}

inline Node mkAnd(std::vector<TNode>& children) {
  std::set<TNode> distinctChildren;
  distinctChildren.insert(children.begin(), children.end());
  
  if (children.size() == 0) {
    return mkTrue();
  }
  
  if (children.size() == 1) {
    return *children.begin();
  }
  
  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = distinctChildren.begin();
  std::set<TNode>::const_iterator it_end = distinctChildren.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}

inline Node mkSortedNode(Kind kind, std::vector<Node>& children) {
  Assert (kind == kind::BITVECTOR_AND ||
          kind == kind::BITVECTOR_OR ||
          kind == kind::BITVECTOR_XOR);
  Assert(children.size() > 0);
  if (children.size() == 1) {
    return children[0]; 
  }
  std::sort(children.begin(), children.end());
  return NodeManager::currentNM()->mkNode(kind, children);
}


inline Node mkNode(Kind kind, std::vector<Node>& children) {
  if (children.size() == 1) {
    return children[0]; 
  }
  return NodeManager::currentNM()->mkNode(kind, children);
}

inline Node mkNode(Kind kind, TNode child) {
  return NodeManager::currentNM()->mkNode(kind, child);
}

inline Node mkNode(Kind kind, TNode child1, TNode child2) {
  return NodeManager::currentNM()->mkNode(kind, child1, child2);
}


inline Node mkSortedNode(Kind kind, TNode child1, TNode child2) {
  Assert (kind == kind::BITVECTOR_AND ||
          kind == kind::BITVECTOR_OR ||
          kind == kind::BITVECTOR_XOR);
  
  if (child1 < child2) {
    return NodeManager::currentNM()->mkNode(kind, child1, child2);
  } else {
    return NodeManager::currentNM()->mkNode(kind, child2, child1);
  }
}

inline Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3) {
  return NodeManager::currentNM()->mkNode(kind, child1, child2, child3);
}


inline Node mkNot(Node child) {
  return NodeManager::currentNM()->mkNode(kind::NOT, child);
}

inline Node mkAnd(TNode node1, TNode node2) {
  return NodeManager::currentNM()->mkNode(kind::AND, node1, node2);
}

inline Node mkOr(TNode node1, TNode node2) {
  return NodeManager::currentNM()->mkNode(kind::OR, node1, node2);
}

inline Node mkXor(TNode node1, TNode node2) {
  return NodeManager::currentNM()->mkNode(kind::XOR, node1, node2);
}


inline Node mkAnd(std::vector<Node>& children) {
  if(children.size() > 1) {
    return NodeManager::currentNM()->mkNode(kind::AND, children);
  } else {
    return children[0];
  }
}

inline Node mkExtract(TNode node, unsigned high, unsigned low) {
  Node extractOp = NodeManager::currentNM()->mkConst<BitVectorExtract>(BitVectorExtract(high, low));
  std::vector<Node> children;
  children.push_back(node);
  return NodeManager::currentNM()->mkNode(extractOp, children);
}

inline Node mkBitOf(TNode node, unsigned index) {
  Node bitOfOp = NodeManager::currentNM()->mkConst<BitVectorBitOf>(BitVectorBitOf(index));
  return NodeManager::currentNM()->mkNode(bitOfOp, node); 
                                        
}


inline Node mkConcat(TNode node, unsigned repeat) {
  Assert (repeat); 
  if(repeat == 1) {
    return node; 
  }
  NodeBuilder<> result(kind::BITVECTOR_CONCAT);
  for (unsigned i = 0; i < repeat; ++i) {
    result << node; 
  }
  Node resultNode = result;
  return resultNode;
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


inline BitVector mkBitVectorOnes(unsigned size) {
  Assert(size > 0); 
  return BitVector(1, Integer(1)).signExtend(size - 1); 
}

inline Node mkOnes(unsigned size) {
  BitVector val = mkBitVectorOnes(size); 
  return NodeManager::currentNM()->mkConst<BitVector>(val); 
}

inline Node mkConst(unsigned size, unsigned int value) {
  BitVector val(size, value);
  return NodeManager::currentNM()->mkConst<BitVector>(val); 
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


inline unsigned isPow2Const(TNode node) {
  if (node.getKind() != kind::CONST_BITVECTOR) {
    return false; 
  }

  BitVector bv = node.getConst<BitVector>();
  return bv.isPow2(); 
}

// neeed a better name, this is not technically a ground term 
inline bool isBVGroundTerm(TNode node) {
  if (node.getNumChildren() == 0) {
    return node.isConst(); 
  }
  
  for (size_t i = 0; i < node.getNumChildren(); ++i) {
    if(! node[i].isConst()) {
      return false;
    }
  }
  return true;
}

inline bool isBVPredicate(TNode node) {
  if (node.getKind() == kind::EQUAL ||
      node.getKind() == kind::BITVECTOR_ULT ||
      node.getKind() == kind::BITVECTOR_SLT ||
      node.getKind() == kind::BITVECTOR_UGT ||
      node.getKind() == kind::BITVECTOR_UGE ||
      node.getKind() == kind::BITVECTOR_SGT ||
      node.getKind() == kind::BITVECTOR_SGE ||
      node.getKind() == kind::BITVECTOR_ULE || 
      node.getKind() == kind::BITVECTOR_SLE ||
      ( node.getKind() == kind::NOT && (node[0].getKind() == kind::EQUAL ||
                                        node[0].getKind() == kind::BITVECTOR_ULT ||
                                        node[0].getKind() == kind::BITVECTOR_SLT ||
                                        node[0].getKind() == kind::BITVECTOR_UGT ||
                                        node[0].getKind() == kind::BITVECTOR_UGE ||
                                        node[0].getKind() == kind::BITVECTOR_SGT ||
                                        node[0].getKind() == kind::BITVECTOR_SGE ||
                                        node[0].getKind() == kind::BITVECTOR_ULE || 
                                        node[0].getKind() == kind::BITVECTOR_SLE)))
    {
      return true; 
    }
  else
    {
      return false; 
    }
}

inline Node mkConjunction(const std::vector<TNode>& nodes) {
  std::vector<TNode> expandedNodes;

  std::vector<TNode>::const_iterator it = nodes.begin();
  std::vector<TNode>::const_iterator it_end = nodes.end();
  while (it != it_end) {
    TNode current = *it;

    if (current != mkTrue()) {
      Assert(isBVPredicate(current));
      expandedNodes.push_back(current);
    }
    ++ it;
  }

  if (expandedNodes.size() == 0) {
    return mkTrue();
  }

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


inline Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */


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
