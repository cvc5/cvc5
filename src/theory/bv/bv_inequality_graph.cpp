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

const TermId CVC4::theory::bv::UndefinedTermId = -1; 
const ReasonId CVC4::theory::bv::UndefinedReasonId = -1;


bool InequalityGraph::addInequality(TNode a, TNode b, TNode reason) {
  Debug("bv-inequality") << "InequlityGraph::addInequality " << a << " " << b << "\n"; 
  TermId id_a = registerTerm(a);
  TermId id_b = registerTerm(b);
  ReasonId id_reason = registerReason(reason);

  if (hasValue(id_a) && hasValue(id_b)) {
    if (getValue(id_a) < getValue(id_b)) {
      // the inequality is true in the current partial model
      // we still add the edge because it may not be true later (cardinality)
      addEdge(id_a, id_b, id_reason);
      return true;
    }
    if (canReach(id_b, id_a)) {
      // we are introducing a cycle; make sure the model reflects this
      Assert (getValue(id_a) >= getValue(id_b)); 
      
      std::vector<ReasonId> conflict;
      conflict.push_back(id_reason); 
      computeExplanation(id_b, id_a, conflict);
      setConflict(conflict); 
      return false; 
    }
  } else {
    bool ok = initializeValues(a, b, id_reason);
    if (!ok) {
      return false;
    }
  }
  // the inequality edge does not exist
  addEdge(id_a, id_b, id_reason);
  BFSQueue queue;
  queue.push(PQueueElement(id_a, getValue(id_a)));
  TermIdSet seen; 
  return computeValuesBFS(queue, seen); 
}

void InequalityGraph::computeExplanation(TermId from, TermId to, std::vector<ReasonId>& explanation) {
  if (to == from || (from == UndefinedTermId && getInequalityNode(to).isConstant())) {
    // we have explained the whole path or reached a constant that forced the value of to
    return;
  }
  
  const Edges& edges = getInEdges(to);
  if (edges.size() == 0) {
    // this can happen when from is Undefined
    Assert (from == UndefinedTermId); 
    return; 
  }
  BitVector max(getBitwidth(to), 0u);
  TermId to_visit = UndefinedTermId;
  ReasonId reason = UndefinedReasonId;
  
  for (Edges::const_iterator it = edges.begin(); it != edges.end(); ++it) {
    TermId next = it->next; 
    if (next == from) {
      explanation.push_back(it->reason); 
      return; 
    }
    if (getValue(next) >= max) {
      max = getValue(next);
      to_visit = it->next;
      reason = it->reason; 
    } 
  }
  Assert(reason != UndefinedReasonId && to_visit != UndefinedTermId);
  explanation.push_back(reason);
  computeExplanation(from, to_visit, explanation); 
}

void InequalityGraph::addEdge(TermId a, TermId b, TermId reason) {
  Edges& out_edges = getOutEdges(a);
  out_edges.push_back(InequalityEdge(b, reason));
  Edges& in_edges = getInEdges(b);
  in_edges.push_back(InequalityEdge(a, reason)); 
}

TermId InequalityGraph::getMaxParent(TermId id) {
  const Edges& in_edges = getInEdges(id);
  Assert (in_edges.size() != 0);
  
  BitVector max(getBitwidth(0), 0u);
  TermId max_id = UndefinedTermId; 
  for (Edges::const_iterator it = in_edges.begin(); it!= in_edges.end(); ++it) {
    // Assert (seen.count(it->next));
    const BitVector& value = getInequalityNode(it->next).getValue();
    if (value >= max) {
      max = value;
      max_id = it->next; 
    }
  }
  Assert (max_id != UndefinedTermId); 
  return max_id; 
}

bool InequalityGraph::hasParents(TermId id) {
  return getInEdges(id).size() != 0; 
}

TermId InequalityGraph::getReasonId(TermId a, TermId b) {
  const Edges& edges = getOutEdges(a);
  for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
    if (it->next == b) {
      return it->reason; 
    }
  }
  Unreachable(); 
}

bool InequalityGraph::computeValuesBFS(BFSQueue& queue, TermIdSet& seen) {
  if (queue.empty())
    return true;

  TermId current = queue.top().id;
  seen.insert(current); 
  queue.pop();
  
  InequalityNode& ineqNode = getInequalityNode(current);
  Debug("bv-inequality-internal") << "InequalityGraph::computeValueBFS \n"; 
  Debug("bv-inequality-internal") << "    processing " << getTerm(current) << "\n"
                                  << "    old value " << ineqNode.getValue() << "\n";
  BitVector zero(getBitwidth(current), 0u);
  BitVector one(getBitwidth(current), 1u); 
  const BitVector min_val = hasParents(current) ? getInequalityNode(getMaxParent(current)).getValue() + one : zero;
  Debug("bv-inequality-internal") << "    min value " << min_val << "\n"; 
                                 
  if (ineqNode.isConstant()) {
    if (ineqNode.getValue() < min_val) {
      Debug("bv-inequality") << "Conflict: constant " << ineqNode.getValue() << "\n"; 
      std::vector<ReasonId> conflict;
      TermId max_parent = getMaxParent(current);
      ReasonId reason_id = getReasonId(max_parent, current);
      conflict.push_back(reason_id); 
      computeExplanation(UndefinedTermId, max_parent, conflict);
      setConflict(conflict); 
      return false; 
    }
  } else {
    // if not constant we can update the value
    if (ineqNode.getValue() < min_val) {
      Debug("bv-inequality-internal") << "Updating " << getTerm(current) <<
        " from " << ineqNode.getValue() << "\n" <<
        " to " << min_val << "\n";  
      ineqNode.setValue(min_val); 
    }
  }
  unsigned bitwidth = min_val.getSize(); 
  BitVector next_min = ineqNode.getValue() + BitVector(bitwidth, 1u); 
  bool overflow = next_min < min_val; 
  const Edges& edges = getOutEdges(current);

  if (edges.size() > 0 && overflow) {
    // we have reached the maximum value
    Debug("bv-inequality") << "Conflict: overflow: " << getTerm(current) << "\n";
    std::vector<ReasonId> conflict; 
    computeExplanation(UndefinedTermId, current, conflict);
    setConflict(conflict); 
    return false;
  }

  for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
    TermId next = it->next;
    if (!seen.count(next)) {
      const BitVector& value = getInequalityNode(next).getValue(); 
      queue.push(PQueueElement(next, value));
    }
  }
  return computeValuesBFS(queue, seen); 
}


bool InequalityGraph::areLessThanInternal(TermId a, TermId b) {
  return getValue(a) < getValue(b); 
}

TermId InequalityGraph::registerTerm(TNode term) {
  if (d_termNodeToIdMap.find(term) != d_termNodeToIdMap.end()) {
    return d_termNodeToIdMap[term]; 
  }

  // store in node mapping
  TermId id = d_termNodes.size();
  d_termNodes.push_back(term);
  d_termNodeToIdMap[term] = id;
  
  // create InequalityNode
  bool isConst = term.getKind() == kind::CONST_BITVECTOR;
  BitVector value(0,0u);  // leaves the value unintialized at this time
  InequalityNode ineq = InequalityNode(id, utils::getSize(term), isConst, value);
  Assert (d_ineqNodes.size() == id); 
  d_ineqNodes.push_back(ineq);
  Assert (d_ineqEdges.size() == id); 
  d_ineqEdges.push_back(Edges());
  Assert(d_parentEdges.size() == id);
  d_parentEdges.push_back(Edges()); 
  Debug("bv-inequality-internal") << "InequalityGraph::registerTerm " << term << "\n"
                                  << "with id " << id << "\n"; 
  return id; 
}

ReasonId InequalityGraph::registerReason(TNode reason) {
  if (d_reasonToIdMap.find(reason) != d_reasonToIdMap.end()) {
    return d_reasonToIdMap[reason]; 
  }
  ReasonId id = d_reasonNodes.size();
  d_reasonNodes.push_back(reason);
  d_reasonToIdMap[reason] = id;
  return id; 
}

TNode InequalityGraph::getReason(ReasonId id) const {
  Assert (d_reasonNodes.size() > id);
  return d_reasonNodes[id]; 
}

TNode InequalityGraph::getTerm(TermId id) const {
  Assert (d_termNodes.size() > id);
  return d_termNodes[id]; 
}

void InequalityGraph::setConflict(const std::vector<ReasonId>& conflict) {
  Assert (!d_inConflict); 
  d_inConflict = true;
  d_conflict.clear(); 
  for (unsigned i = 0; i < conflict.size(); ++i) {
    d_conflict.push_back(getReason(conflict[i])); 
  }
  if (Debug.isOn("bv-inequality")) {
    Debug("bv-inequality") << "InequalityGraph::setConflict \n";
    for (unsigned i = 0; i < d_conflict.size(); ++i) {
      Debug("bv-inequality") << "   " << d_conflict[i] <<"\n"; 
    }
  }
}

void InequalityGraph::getConflict(std::vector<TNode>& conflict) {
  for (unsigned i = 0; i < d_conflict.size(); ++i) {
    conflict.push_back(d_conflict[i]); 
  }
}

bool InequalityGraph::canReach(TermId from, TermId to) {
  if (from == to )
    return true;
  
  TermIdSet seen;
  TermIdQueue queue;
  queue.push(from); 
  bfs(seen, queue);
  if (seen.count(to)) {
    return true; 
  }
  return false; 
}

void InequalityGraph::bfs(TermIdSet& seen, TermIdQueue& queue) {
  if (queue.empty())
    return;
  
  TermId current = queue.front();
  queue.pop();

  const Edges& edges = getOutEdges(current);
  for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
    TermId next = it->next;
    if(seen.count(next) == 0) {
      seen.insert(next);
      queue.push(next); 
    }
  }
  bfs(seen, queue);
}

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

bool InequalityGraph::hasValue(TermId id) const {
  return getInequalityNode(id).getValue() != BitVector(0, 0u); 
}

bool InequalityGraph::initializeValues(TNode a, TNode b, TermId reason_id) {
  TermId id_a = registerTerm(a);
  TermId id_b = registerTerm(b);
  
  InequalityNode& ineq_a = getInequalityNode(id_a);
  InequalityNode& ineq_b = getInequalityNode(id_b);
  // FIXME: dumb case splitting 
  if (ineq_a.isConstant() && ineq_b.isConstant()) {
    Assert (a.getConst<BitVector>() < b.getConst<BitVector>());
    ineq_a.setValue(a.getConst<BitVector>());
    ineq_b.setValue(b.getConst<BitVector>());
    return true; 
  }
  
  if (ineq_a.isConstant()) {
    ineq_a.setValue(a.getConst<BitVector>());
  }
  if (ineq_b.isConstant()) {
    const BitVector& const_val = b.getConst<BitVector>(); 
    ineq_b.setValue(const_val);
    // check for potential underflow
    if (hasValue(id_a) && ineq_a.getValue() > const_val) {
      // must be a conflict because we have as an invariant that a will have the min
      // possible value for a. 
      std::vector<ReasonId> conflict;
      conflict.push_back(reason_id);
      // FIXME: this will not compute the most precise conflict
      // could be fixed by giving computeExplanation a bound (i.e. the size of const_val)
      computeExplanation(UndefinedTermId, id_a, conflict);
      setConflict(conflict); 
      return false; 
    }
  }

  BitVector one(getBitwidth(id_a), 1u);
  BitVector zero(getBitwidth(id_a), 0u);
  
  if (!hasValue(id_a) && !hasValue(id_b)) {
    // initialize to the minimum possible values
    ineq_a.setValue(zero); 
    ineq_b.setValue(one); 
  }
  else if (!hasValue(id_a) && hasValue(id_b)) {
    const BitVector& b_value = ineq_b.getValue();
    if (b_value == zero) {
      if (ineq_b.isConstant()) {
        Debug("bv-inequality") << "Conflict: underflow " << getTerm(id_a) <<"\n";
        std::vector<ReasonId> conflict;
        conflict.push_back(reason_id);
        setConflict(conflict); 
        return false; 
      }
      // otherwise we attempt to increment b
      ineq_b.setValue(one); 
    }
    // if a has no value then we can assign it to whatever we want
    // to maintain the invariant that each value has the lowest value
    // we assign it to zero 
    ineq_a.setValue(zero); 
  } else if (hasValue(id_a) && !hasValue(id_b)) {
    const BitVector& a_value = ineq_a.getValue();
    if (a_value + one < a_value) {
      return false; 
    }
    ineq_b.setValue(a_value + one); 
  }
  return true; 
}
