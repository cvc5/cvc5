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
#include "theory/bv/bv_to_bool.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

void BvToBoolVisitor::addToCache(TNode bv_term, Node bool_term) {
  Assert (!hasCache(bv_term));
  Assert (bool_term.getType().isBoolean()); 
  d_cache[bv_term] = bool_term; 
}

Node BvToBoolVisitor::getCache(TNode bv_term) const {
  Assert (hasCache(bv_term));
  return d_cache.find(bv_term)->second; 
}

bool BvToBoolVisitor::hasCache(TNode bv_term) const {
  Assert (bv_term.getType().isBitVector()); 
  return d_cache.find(bv_term) != d_cache.end(); 
}

void BvToBoolVisitor::start(TNode node) {}

bool BvToBoolVisitor::alreadyVisited(TNode current, TNode parent) {
  return d_visited.find(current) != d_visited.end(); 
}

bool BvToBoolVisitor::isConvertibleToBool(TNode current) {
  TypeNode type = current.getType(); 
  if (current.getNumChildren() == 0 && type.isBitVector()) {
    return type.getBitVectorSize() == 1; 
  }

  if (current.getKind() == kind::NOT) {
    current = current[0];
  }
  Kind kind = current.getKind();
  // checking bit-vector kinds 
  if (kind == kind::BITVECTOR_OR ||
      kind == kind::BITVECTOR_AND ||
      kind == kind::BITVECTOR_XOR ||
      kind == kind::BITVECTOR_NOT ||
      // kind == kind::BITVECTOR_PLUS ||
      // kind == kind::BITVECTOR_SUB ||
      // kind == kind::BITVECTOR_NEG ||
      kind == kind::BITVECTOR_ULT ||
      kind == kind::BITVECTOR_ULE ||
      kind == kind::EQUAL) {
    return current[0].getType().getBitVectorSize() == 1; 
  }
  if (kind == kind::ITE &&
      type.isBitVector()) {
    return type.getBitVectorSize() == 1; 
  }
  return false; 
}

Node BvToBoolVisitor::convertToBool(TNode current) {
  Kind kind = current.getKind();
  if (kind == kind::BITVECTOR_ULT) {
    TNode a = getCache(current[0]);
    TNode b = getCache(current[1]);
    Node a_eq_0 = utils::mkNode(kind::EQUAL, a, d_zero);
    Node b_eq_1 = utils::mkNode(kind::EQUAL, b, d_one);
    Node new_current = utils::mkNode(kind::AND, a_eq_0, b_eq_1);
    return new_current; 
  }
  if (kind == kind::BITVECTOR_ULE) {
    TNode a = getCache(current[0]);
    TNode b = getCache(current[1]);
    Node a_eq_0 = utils::mkNode(kind::EQUAL, a, d_zero);
    Node b_eq_1 = utils::mkNode(kind::EQUAL, b, d_one);
    Node a_lt_b = utils::mkNode(kind::AND, a_eq_0, b_eq_1); 
    Node a_eq_b = utils::mkNode(kind::EQUAL, a, b);
    Node new_current = utils::mkNode(kind::OR, a_lt_b, a_eq_b);
    return new_current; 
  }

  
  Kind new_kind; 
  switch (kind) {
  case kind::BITVECTOR_OR :
    new_kind = kind::OR;
  case kind::BITVECTOR_AND:
    new_kind =  kind::AND;
  case kind::BITVECTOR_XOR:
    new_kind = kind::XOR;
  case kind::BITVECTOR_NOT:
    new_kind =  kind::NOT;
  case kind::BITVECTOR_ULT:
  default:
    Unreachable();  
  }
  NodeBuilder<> builder(new_kind);
  for (unsigned i = 0; i < current.getNumChildren(); ++i) {
    builder << getCache(current[i]); 
  }
  return builder; 
}

void BvToBoolVisitor::visit(TNode current, TNode parent) {
  Assert (!alreadyVisited(current, parent));
  d_visited.insert(current);
  
  if (current.getNumChildren() == 0 &&
      isConvertibleToBool(current)) {
    Node bool_current; 
    if (current.getKind() == kind::CONST_BITVECTOR) {
      bool_current = current == d_one? utils::mkTrue() : utils::mkFalse(); 
    } else {
      bool_current = utils::mkNode(kind::EQUAL, current, d_one); 
    }
    addToCache(current, bool_current);
    return; 
  }

  // if it has more than one child
  if (isConvertibleToBool(current)) {
    Node bool_current = convertToBool(current); 
    addToCache(current, bool_current); 
  } else {
    NodeBuilder<> builder(current.getKind());
    for (unsigned i = 0; i < current.getNumChildren(); ++i) {
      Node converted = getCache(current[i]);
      if (converted.getType() == current[i].getType()) {
        builder << converted; 
      } else {
        builder << current[i]; 
      }
    }
    Node result = builder;
    addToCache(current, result); 
  }
}

BvToBoolVisitor::return_type BvToBoolVisitor::done(TNode node) {
  Assert (hasCache(node)); 
  return getCache(node); 
}

Node BvToBoolPreprocessor::liftBoolToBV(TNode assertion) {
  Node result = NodeVisitor<BvToBoolVisitor>::run(d_visitor, assertion);
  return result; 
}
