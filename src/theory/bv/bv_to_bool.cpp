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

void BvToBoolVisitor::storeBvToBool(TNode bv_term, Node bool_term) {
  Assert (!hasBoolTerm(bv_term));
  Assert (bool_term.getType().isBoolean()); 
  d_bvToBoolTerm[bv_term] = bool_term; 
}

Node BvToBoolVisitor::getBoolTerm(TNode bv_term) const {
  Assert(hasBoolTerm(bv_term));
  return d_bvToBoolTerm.find(bv_term)->second; 
}

bool BvToBoolVisitor::hasBoolTerm(TNode bv_term) const {
  Assert (bv_term.getType().isBitVector()); 
  return d_bvToBoolTerm.find(bv_term) != d_bvToBoolTerm.end(); 
}

void BvToBoolVisitor::addToCache(TNode term, Node new_term) {
  Assert (new_term != Node()); 
  Assert (!hasCache(term));
  d_cache[term] = new_term; 
}

Node BvToBoolVisitor::getCache(TNode term) const {
  if (!hasCache(term)) {
    return term; 
  }
  return d_cache.find(term)->second; 
}

bool BvToBoolVisitor::hasCache(TNode term) const {
  return d_cache.find(term) != d_cache.end(); 
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
      kind == kind::BITVECTOR_ULT ||
      kind == kind::BITVECTOR_ULE ||
      kind == kind::EQUAL) {
    // we can convert it to bool if all of the children can also be converted
    // to bool
    if (! current[0].getType().getBitVectorSize() == 1)
      return false; 
    for (unsigned i = 0; i < current.getNumChildren(); ++i) {
      // we assume that the children have been visited
      if (!hasBoolTerm(current[i]))
        return false; 
    }
    return true; 
  }
  if (kind == kind::ITE &&
      type.isBitVector()) {
    return type.getBitVectorSize() == 1 && hasBoolTerm(current[1]) && hasBoolTerm(current[2]); 
  }
  return false; 
}


Node BvToBoolVisitor::convertToBool(TNode current) {
  Debug("bv-to-bool") << "BvToBoolVisitor::convertToBool (" << current << ") "; 
  Kind kind = current.getKind();

  Node new_current; 
  if (current.getNumChildren() == 0) {
    if (current.getKind() == kind::CONST_BITVECTOR) {
      new_current = current == d_one? utils::mkTrue() : utils::mkFalse(); 
    } else {
      new_current = utils::mkNode(kind::EQUAL, current, d_one); 
    }
    Debug("bv-to-bool") << "=> " << new_current << "\n"; 
  } else if (kind == kind::BITVECTOR_ULT) {
    TNode a = getBoolTerm(current[0]);
    TNode b = getBoolTerm(current[1]);
    Node a_eq_0 = utils::mkNode(kind::EQUAL, a, d_zero);
    Node b_eq_1 = utils::mkNode(kind::EQUAL, b, d_one);
    new_current = utils::mkNode(kind::AND, a_eq_0, b_eq_1);
  }  else if (kind == kind::BITVECTOR_ULE) {
    TNode a = getBoolTerm(current[0]);
    TNode b = getBoolTerm(current[1]);
    Node a_eq_0 = utils::mkNode(kind::EQUAL, a, d_zero);
    Node b_eq_1 = utils::mkNode(kind::EQUAL, b, d_one);
    Node a_lt_b = utils::mkNode(kind::AND, a_eq_0, b_eq_1); 
    Node a_eq_b = utils::mkNode(kind::EQUAL, a, b);
    new_current = utils::mkNode(kind::OR, a_lt_b, a_eq_b);
  } else if (kind == kind::ITE) {
    TNode cond = current[0];
    TNode a = getBoolTerm(current[1]);
    TNode b = getBoolTerm(current[2]);
    new_current = utils::mkNode(kind::ITE, cond, a, b);
  } else {
    Kind new_kind; 
    switch (kind) {
    case kind::BITVECTOR_OR :
      new_kind = kind::OR;
      break; 
    case kind::BITVECTOR_AND:
      new_kind =  kind::AND;
      break; 
    case kind::BITVECTOR_XOR:
      new_kind = kind::XOR;
      break; 
    case kind::BITVECTOR_NOT:
      new_kind =  kind::NOT;
      break; 
    case kind::EQUAL:
      new_kind = kind::IFF;
      break; 
    default:
      Unreachable("Unknown kind ", kind);  
    }
    NodeBuilder<> builder(new_kind);
    if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
      builder << current.getOperator();
    }
    for (unsigned i = 0; i < current.getNumChildren(); ++i) {
      builder << getBoolTerm(current[i]); 
    }
    new_current = builder;
  }
  
  Debug("bv-to-bool") << "=> " << new_current << "\n";
  if (current.getType().isBitVector()) {
    storeBvToBool(current, new_current); 
  } else {
    addToCache(current, new_current); 
  }
  return new_current; 
}

void BvToBoolVisitor::visit(TNode current, TNode parent) {
  Debug("bv-to-bool") << "BvToBoolVisitor visit (" << current << ", " << parent << ")\n"; 
  Assert (!alreadyVisited(current, parent));
  d_visited.insert(current);

  Node result; 
  // if it has more than one child
  if (isConvertibleToBool(current)) {
    result = convertToBool(current); 
  } else {
    if (current.getNumChildren() == 0) {
      result = current; 
    } else {
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        Node converted = getCache(current[i]);
        if (converted.getType() == current[i].getType()) {
          builder << converted; 
        } else {
          builder << current[i]; 
        }
      }
      result = builder;
    }
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
