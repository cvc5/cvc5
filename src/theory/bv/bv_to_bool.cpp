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

void BvToBoolVisitor::storeBvToBool(TNode bv_term, TNode bool_term) {
  Assert (bv_term.getType().isBitVector() &&
          bv_term.getType().getBitVectorSize() == 1);
  Assert (bool_term.getType().isBoolean() &&  d_bvToBoolMap.find(bv_term) == d_bvToBoolMap.end());
  d_bvToBoolMap[bv_term] = bool_term; 
}

Node BvToBoolVisitor::getBoolForBvTerm(TNode node) {
  Assert (d_bvToBoolMap.find(node) != d_bvToBoolMap.end());
  return d_bvToBoolMap[node]; 
}

bool BvToBoolVisitor::alreadyVisited(TNode current, TNode parent) {
  return d_cache.find(current) != d_cache.end(); 
}

bool BvToBoolVisitor::isConvertibleBvAtom(TNode node) {
  Kind kind = node.getKind();
  return (kind == kind::BITVECTOR_ULT ||
          kind == kind::BITVECTOR_ULE ||
          kind == kind::EQUAL) &&
    node[0].getType().isBitVector() &&
    node[0].getType().getBitVectorSize() == 1; 
}

bool BvToBoolVisitor::isConvertibleBvTerm(TNode node) {
  // we have already converted it and the result is cached
  if (d_bvToBoolMap.find(node) != d_bvToBoolMap.end()) {
    return true;
  }
  
  Kind kind = node.getKind();
  if (!node.getType().isBitVector() || node.getType().getBitVectorSize() != 1)
    return false;
  
  if (kind == kind::CONST_BITVECTOR) {
    return true; 
  }

  if (kind == kind::BITVECTOR_AND || kind == kind::BITVECTOR_OR ||
      kind == kind::BITVECTOR_NOT || kind == kind::BITVECTOR_XOR) {
    for (unsigned i = 0; i < node.getNumChildren(); ++i) {
      if (!isConvertibleBvTerm(node[i]))
        return false; 
    }
    return true; 
  }
  return false; 
}

Node BvToBoolVisitor::convertBvAtom(TNode node) {
  Assert (node.getType().isBoolean());
  Kind kind = node.getKind();
  Node result; 
  switch(kind) {
  case kind::BITVECTOR_ULT: {
    TNode a = getBoolForBvTerm(node[0]);
    TNode b = getBoolForBvTerm(node[1]);
    Node a_eq_0 = utils::mkNode(kind::EQUAL, a, d_zero);
    Node b_eq_1 = utils::mkNode(kind::EQUAL, b, d_one);
    result = utils::mkNode(kind::AND, a_eq_0, b_eq_1);
    break;
  }
  case kind::BITVECTOR_ULE: {
   TNode a = getBoolForBvTerm(node[0]);
   TNode b = getBoolForBvTerm(node[1]);
   Node a_eq_0 = utils::mkNode(kind::EQUAL, a, d_zero);
   Node b_eq_1 = utils::mkNode(kind::EQUAL, b, d_one);
   Node a_lt_b = utils::mkNode(kind::AND, a_eq_0, b_eq_1); 
   Node a_eq_b = utils::mkNode(kind::EQUAL, a, b);
   result = utils::mkNode(kind::OR, a_lt_b, a_eq_b);    
   break;
  }
  case kind::EQUAL: {
    TNode a = getBoolForBvTerm(node[0]);
    TNode b = getBoolForBvTerm(node[1]);
    result = utils::mkNode(kind::IFF, a, b); 
    break;
  }
  default:
    Unhandled(); 
  }
  Assert (result != Node());
  return result;
}

Node BvToBoolVisitor::convertBvTerm(TNode node) {
  Assert (node.getType().isBitVector() &&
          node.getType().getBitVectorSize() == 1);
  Kind kind = node.getKind(); 

  if (node.getNumChildren() == 0) {
    if (node.getKind() == kind::VARIABLE) {
      return getBoolForBvTerm(node);
    }
    if (node.getKind() == kind::CONST_BITVECTOR) {
      return (node == d_one ? utils::mkTrue() : utils::mkFalse());
    }
  }
  
  if (kind == kind::ITE) {
    TNode cond = getCache(node[0]);
    TNode true_branch = getBoolForBvTerm(node[1]);
    TNode false_branch = getBoolForBvTerm(node[2]);
    Node result = utils::mkNode(kind::ITE, cond, true_branch, false_branch);
    storeBvToBool(node, result);
    return result; 
  }
  
  Kind new_kind; 
  switch(kind) {
  case kind::BITVECTOR_OR:
    new_kind = kind::OR;
    break;
  case kind::BITVECTOR_AND:
    new_kind = kind::AND;
    break;
  case kind::BITVECTOR_XOR:
    new_kind = kind::XOR;
    break;
  case kind::BITVECTOR_NOT:
    new_kind = kind::NOT;
    break;
  default:
    Unhandled(); 
  }

  NodeBuilder<> builder(new_kind);
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    builder << getBoolForBvTerm(node[i]); 
  }
  Node result = builder;
  storeBvToBool(node, result);
  return result; 
}

void BvToBoolVisitor::check(TNode current, TNode parent) {
  if (d_bvToBoolMap.find(current) != d_bvToBoolMap.end()) {
    if (!isConvertibleBvTerm(parent) && !isConvertibleBvAtom(parent)) {
      Debug("bv-to-bool") << "BvToBoolVisitor::check " << current << " in non boolean context: \n"
                          << "           " << parent << "\n"; 
    }
  }
}

void BvToBoolVisitor::visit(TNode current, TNode parent) {
  Debug("bv-to-bool") << "BvToBoolVisitor visit (" << current << ", " << parent << ")\n"; 
  Assert (!alreadyVisited(current, parent) &&
          !hasCache(current));
  
  Node result;

  // make sure that the bv terms we are replacing to not occur in other contexts
  check(current, parent); 
  
  if (isConvertibleBvAtom(current)) {
    result = convertBvAtom(current); 
  } else if (isConvertibleBvTerm(current)) {
    result = convertBvTerm(current); 
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
        Assert (converted.getType() == current[i].getType()); 
        builder << converted; 
      }
      result = builder;
    }
  }
  Assert (result != Node()); 
  addToCache(current, result);
}


BvToBoolVisitor::return_type BvToBoolVisitor::done(TNode node) {
  Assert (hasCache(node)); 
  return getCache(node); 
}

bool BvToBoolPreprocessor::matchesBooleanPatern(TNode current) {
  // we are looking for something of the type (= (bvvar 1) (some predicate))
  if (current.getKind() == kind::IFF &&
      current[0].getKind() == kind::EQUAL &&
      current[0][0].getType().isBitVector() &&
      current[0][0].getType().getBitVectorSize() == 1 &&
      current[0][0].getKind() == kind::VARIABLE &&
      current[0][1].getKind() == kind::CONST_BITVECTOR) {
    return true; 
  }    
  return false; 
}


void BvToBoolPreprocessor::liftBoolToBV(const std::vector<TNode>& assertions, std::vector<Node>& new_assertions) {
  TNodeNodeMap candidates;
  for (unsigned i = 0; i < assertions.size(); ++i) {
    if (matchesBooleanPatern(assertions[i])) {
      TNode assertion = assertions[i]; 
      TNode bv_var = assertion[0][0];
      Assert (bv_var.getKind() == kind::VARIABLE &&
              bv_var.getType().isBitVector() &&
              bv_bar.getType().getBitVectorSize() == 1);
      TNode bool_cond = assertion[1];
      Assert (bool_cond.getType().isBoolean());
      if (candidates.find(bv_var) == candidates.end()) {
        Debug("bv-to-bool") << "BBvToBoolPreprocessor::liftBvToBoolBV candidate: " << bv_var <<"\n"; 
        candidates[bv_var] = bool_cond;
      } else {
        Debug("bv-to-bool") << "BvToBoolPreprocessor::liftBvToBoolBV multiple def " << bv_var <<"\n"; 
      }
    }
  }
  
  BvToBoolVisitor bvToBoolVisitor(candidates); 
  for (unsigned i = 0; i < assertions.size(); ++i) {
    Node new_assertion = NodeVisitor<BvToBoolVisitor>::run(bvToBoolVisitor,
                                              assertions[i]);
    new_assertions.push_back(new_assertion); 
  }
}
