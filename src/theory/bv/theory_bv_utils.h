/*********************                                                        */
/*! \file theory_bv_utils.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#include <vector>
#include "expr/node_manager.h"

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

inline Node mkConst(const BitVector& value) {
  return NodeManager::currentNM()->mkConst<BitVector>(value);
}


}
}
}
}
