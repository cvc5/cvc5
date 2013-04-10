/*********************                                                        */
/*! \file bv_to_bool.h
 ** \verbatim
 ** Original author: Liana Hadarean 
 ** Major contributors: None. 
 ** Minor contributors (to current version): None. 
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **
 ** Preprocessing pass that lifts bit-vectors of size 1 to booleans. 
 **/


#include "util/node_visitor.h"


void BVToBoolVisitor::addBvToBool(TNode bv_term, Node bool_term) {
  Assert (!hasBoolTerm(bv_term));
  Assert (bool_term.getType().isBoolean()); 
  d_bvToBool[bv_term] = bool_term; 
}

Node BVToBoolVisitor::toBoolTerm(TNode bv_term) const {
  Assert (hasBoolTerm(bv_term));
  return d_bvToBool.find(bv_term)->second; 
}

bool BVToBoolVisitor::hasBoolTerm(TNode bv_term) const {
  Assert (bv_term.getType().isBitVector()); 
  return d_bvToBool.find(bv_term) != d_bvToBool.end(); 
}

void BVToBoolVisitor::start(TNode node) {}

return_type BVToBoolVisitor::done(TNode node) {
  return 0; 
}

bool BvToBoolVisitor::alreadyVisited(TNode current, TNode parent) {
  return d_visited.find(current) != d_visited.end(); 
}

bool BvToBoolVisitor::isConvertibleToBool(TNode current) {
  if (current.getNumChildren() == 0) {
    return current.getType().getBitVectorSize() == 1; 
  }

  Kind kind = current.getKind();
  if (kind == kind::BITVECTOR_OR ||
      kind == kind::BITVECTOR_AND ||
      kind == kind::BITVECTOR_XOR ||
      kind == kind::BITVECTOR_NOT ||
      kind == kind::BITVECTOR_ADD ||
      kind == kind::BITVECTOR_NOT ||
      kind == kind::BITVECTOR_ULT ||
      kind == kind::BITVECTOR_ULE) {
    return current[0].getType().getBitVectorSize() == 1; 
  }
}

void BvToBoolVisitor::visit(TNode current, TNode parent) {
  Assert (!alreadyVisited());
  
  if (current.getType().isBitVector() &&
      current.getType().getBitVectorSize() != 1) {
    // we only care about bit-vector terms of size 1
    d_visited.push_back(current);
    return; 
  }
  
  d_visited.insert(current);
  
  if (current.getNumChildren() == 0 &&
      current.getType().isBitVector() &&
      current.getType().getBitVectorSize() == 1) {
    Node bool_current; 
    if (current.getKind() == kind::CONST_BITVECTOR) {
      bool_current = current == d_one? utils::mkTrue() : utils::mkFalse(); 
    } else {
      bool_current = utils::mkNode(kind::EQUAL, current, d_one); 
    }
    addBvToBool(current, current_eq_one);
    return; 
  }

  // if it has more than one child
  if (current.getKind().isBitVectorKind() && isConvertibleToBool(current)) {
    Kind bool_kind = boolToBvKind(current.getKind());
    NodeBuilder<> builder(bool_kind); 
    for (unsigned i = 0; i < current.getNumChildren(); ++i) {
      builder << toBoolTerm(current[i]); 
    }
    Node bool_current = builder;
    addBvToBool(current, bool_current); 
  } 
}

return_type BvToBoolVisitor::done(TNode node) {}

