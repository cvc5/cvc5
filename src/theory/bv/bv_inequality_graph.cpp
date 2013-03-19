/*********************                                                        */
/*! \file bv_inequality_graph.cpp
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A graph representation of the currently asserted bv inequalities. 
 **
 ** A graph representation of the currently asserted bv inequalities. 
 **/

#include "theory/bv/bv_inequality_graph.h"
#include "theory/bv/theory_bv_utils.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

bool InequalityGraph::addInequality(TNode a, TNode b, TNode reason) {
  TermId id_a = registerTerm(a);
  TermId id_b = registerTerm(b);
  ReasonId id_reason = registerReason(reason);
  return addInequalityInternal(id_a, id_b, id_reason);
}


bool InequalityGraph::addInequalityInternal(TermId a, TermId b, TermId reason) {
  if (getValue(a) < getValue(b)) {
    // the inequality is true in the current partial model
    return true;
  }
  if (getValue(b) < getValue(a)) {
    // the inequality is false in the current partial model
    std::vector<ReasonId> conflict; 
    computeExplanation(b, a, conflict); 
    return false; 
  }
  // the inequality edge does not exist
  addEdge(a, b, reason);
  BFSQueue queue;
  queue.push(a); 
  return computeValuesBFS(queue); 
}

void InequalityGraph::computeConflict(TermId from, TermId to, std::vector<ReasonId>& explanation) {
  if (to == from)
    return;
  const Edges& edges = getInEdges(to);
  BitVector max(getBitwidth(a), 0);
  TermId to_visit = UndefinedTermId;
  ReasonId reason = UndefinedReasonId;
  
  for (Edges::const_iterator it = edges.begin(); it != edges.end(); ++it) {
    TermId next = it->next; 
    if (next == from) {
      explanation.push_back(it->reason); 
      return; 
    }
    if (getValue(next) >= max) {
      max = it->value;
      to_visit = it->next;
      reason = it->reason; 
    } 
  }
  Assert(reason != UndefinedReasonId && to_visit != UndefinedTermId);
  explanation.push_back(reason);
  computeConflict(from, to_visit, explanation); 
}

void InequalityGraph::addEdge(TermId a, TermId b, TermId reason) {
  Edges& out_edges = getEdges(a);
  edges.push_back(InequalityEdge(b, reason));
  Edges& in_edges = getParentEdges(b);
  edges.push_back(InequalityEdge(a, reason)); 
}

bool InequalityGraph::computeValuesBFS(BitVector& min_val, BFSQueue& queue, TermIdSet& seen) {
  if (queue.empty())
    return true;
  
  TermId current = queue.top().id;
  seen.insert(current); 
  queue.pop();
  
  InequalityNode& ineqNode = getInequalityNode(current);
  if (ineqNode.isConstant()) {
    if (ineqNode.getValue() < min_val) {
      // we have a conflict 
      return false; 
    }
  } else {
    // if not constant we can update the value
    if (ineqNode.getValue() < min_val) {
      ineqNode.setValue(min_val); 
    }
  }
  BitVector next_min = ineqNode.getValue() + 1; 
  bool overflow = next_min < min_val; 
  const Edges& edges = getEdges(current);

  if (edges.size() > 0 && overflow) {
    // we have reached the maximum value
    computeConflict(); 
    return false;
  }
  // TODO: update key, maybe
  for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
    TermId next = it->next;
    if (!seen.contains(next)) {
      BitVector& value = getInequalityNode(next).getValue(); 
      queue.push(PQueueElement(next, value));
    }
  }
  return computeValuesBFS(next_min, queue, seen); 
}


bool InequalityGraph::areLessThanInternal(TermId a, TermId b) {
  return getValue(a) < getValue(b); 
}

TermId InequalitySolver::registerTerm(TNode term) {
  if (d_termNodeToIdMap.find(term) != d_termNodeToIdMap.end()) {
    return d_termNodeToIdMap[term]; 
  }

  // store in node mapping
  TermId id = d_termNodes.size();
  d_termNodes.push_back(term);
  d_termNodeToIdMap[term] = id;
  
  // create InequalityNode
  bool isConst = term.getKind() == kind::CONST_BITVECTOR;
  BitVector value = isConst? term.getConst<BitVector>() : BitVector(utils::getSize(term),0); 
  InequalityNode ineq = InequalityNode(id, utils::getSize(term), isConst, value);
  Assert (d_ineqNodes.size() == id); 
  d_ineqNodes.push_back(ineq);
  Assert (d_ineqEdges.size() == id); 
  d_ineqEdges.push_back(Edges());
  Assert(d_parentEdges.size() == id);
  d_parentEdges.push_back(Edges()); 
  return id; 
}

ReasonId InequalitySolver::registerReason(TNode reason) {
  if (d_reasonToIdMap.find(reason) != d_reasonToIdMap.end()) {
    return d_reasonToIdMap[reason]; 
  }
  ReasonId id = d_reasonNodes.size();
  d_reasonNodes.push_back(reason);
  d_reasonToIdMap[reason] = id;
  return id; 
}

TNode InequalitySolver::getReason(ReasonId id) const {
  Assert (d_reasonNodes.size() > id);
  return d_reasonNodes[id]; 
}

TNode InequalitySolver::getTerm(TermId id) const {
  Assert (d_termNodes.size() > id);
  return d_termNodes[id]; 
}

void InequalitySolver::setConflict(const std::vector<ReasonId>& conflict) {
  Assert (!d_inConflict); 
  d_inConflict = true;
  d_conflict.clear(); 
  for (unsigned i = 0; i < conflict.size(); ++i) {
    d_conflict.push_back(getReason(conflict[i])); 
  }
}

void InequalitySolver::getConflict(std::vector<TNode>& conflict) {
  for (unsigned i = 0; i < d_conflict.size(); ++it) {
    conflict.push_back(d_conflict[i]); 
  }
}

// bool InequalityGraph::canReach(TermId from, TermId to) {
//   TermIdSet visited;
//   bfs(start, seen);
//   if (seen.constains(to)) {
//     return true; 
//   }
// }

// bool InequalityGraph::bfs(TermId to, TermIdSet& seen, TermIdQueue& queue) {
//   if (queue.empty())
//     return;
  
//   TermId current = queue.front();
//   queue.pop();
//   if (current = to) {
//     return true; 
//   }
//   const Edges& edges = getEdges(current);
//   for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
//     TermId next = it->next;
//     if(!seen.contains(next)) {
//       seen.insert(next);
//       queue.push(next); 
//     }
//   }
//   return bfs(seen, queue);
// }

// void InequalityGraph::getPath(TermId to, TermId from, const TermIdSet& seen, std::vector<ReasonId> explanation) {
//   // traverse parent edges
//   const Edges& out = getOutEdges(to);
//   for (Edges::const_iterator it = out.begin(); it != out.end(); ++it) {
//     if (seen.find(it->next)) {
//       path.push_back(it->reason); 
//       getPath(it->next, from, seen, path);
//       return; 
//     }
//   }
// }

// bool InequalityGraph::initializeValues(TNode a, TNode b) {
//   TermId id_a = registerTerm(a);
//   TermId id_b = registerTerm(b);
//   if (!hasValue(id_a) && !hasValue(id_b)) {
//     InequalityNode& ineq_a = getInequalityNode(id_a);
//     ineq_a.setValue(BiVector(utils::getSize(a), 0));
//     InequalityNode& ineq_b = getInequalityNode(id_b);
//     ineq_a.setValue(BiVector(utils::getSize(a), 1));
//   }
//   if (!hasValue(id_a) && hasValue(id_b)) {
//     BitVector& b_value = getValue(id_b);
//     if (b_value == 0) {
//       return false; 
//     }
//     InequalityNode& ineq_a = getInequalityNode(id_a);
//     ineq_a.setValue(b_value - 1); 
//   }
//   if (hasValue(id_a) && !hasValue(id_b)) {
//     BitVector& a_value = getValue(id_a);
//     if (a_value + 1 < a_value) {
//       return false; 
//     }
//     InequalityNode& ineq_b = getInequalityNode(id_b);
//     ineq_b.setValue(a_value + 1); 
//   }
//   return true; 
// }
