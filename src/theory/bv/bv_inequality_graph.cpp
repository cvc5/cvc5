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
const ReasonId CVC4::theory::bv::AxiomReasonId = -2;


BitVector InequalityGraph::maxValue(unsigned bitwidth) {
  if (d_signed) {
    return BitVector(1, 0u).concat(~BitVector(bitwidth - 1, 0u)); 
  }
  return ~BitVector(bitwidth, 0u);
}

BitVector InequalityGraph::minValue(unsigned bitwidth) {
  if (d_signed) {
    return ~BitVector(bitwidth, 0u); 
  } 
  return BitVector(bitwidth, 0u);
}

TermId InequalityGraph::getMaxValueId(unsigned bitwidth) {
  BitVector bv = maxValue(bitwidth); 
  Node max = utils::mkConst(bv); 
  
  if (d_termNodeToIdMap.find(max) == d_termNodeToIdMap.end()) {
    TermId id = d_termNodes.size(); 
    d_termNodes.push_back(max);
    d_termNodeToIdMap[max] = id;
    InequalityNode node(id, bitwidth, true, bv);
    d_ineqNodes.push_back(node); 

    // although it will never have out edges we need this to keep the size of
    // d_termNodes and d_ineqEdges in sync
    d_ineqEdges.push_back(Edges());
    return id; 
  }
  return d_termNodeToIdMap[max]; 
}

TermId InequalityGraph::getMinValueId(unsigned bitwidth) {
  BitVector bv = minValue(bitwidth); 
  Node min = utils::mkConst(bv); 

  if (d_termNodeToIdMap.find(min) == d_termNodeToIdMap.end()) {
    TermId id = d_termNodes.size(); 
    d_termNodes.push_back(min);
    d_termNodeToIdMap[min] = id;
    d_ineqEdges.push_back(Edges());
    InequalityNode node = InequalityNode(id, bitwidth, true, bv);
    d_ineqNodes.push_back(node); 
    return id; 
  }
  return d_termNodeToIdMap[min]; 
}

bool InequalityGraph::addInequality(TNode a, TNode b, bool strict, TNode reason) {
  Debug("bv-inequality") << "InequlityGraph::addInequality " << a << " " << b << "strict: " << strict << "\n"; 

  TermId id_a = registerTerm(a);
  TermId id_b = registerTerm(b);
  ReasonId id_reason = registerReason(reason);

  Assert (!(isConst(id_a) && isConst(id_b))); 
  BitVector a_val = getValue(id_a);
  BitVector b_val = getValue(id_b);
    
  unsigned bitwidth = utils::getSize(a); 
  BitVector diff = strict ? BitVector(bitwidth, 1u) : BitVector(bitwidth, 0u);

  if (a_val + diff < a_val) {
    // we have an overflow
    std::vector<ReasonId> conflict;
    conflict.push_back(id_reason);
    computeExplanation(UndefinedTermId, id_a, conflict);
    setConflict(conflict);
    return false; 
  }
  
  if (a_val + diff <= b_val) {
    // the inequality is true in the current partial model
    // we still add the edge because it may not be true later (cardinality)
    addEdge(id_a, id_b, strict, id_reason);
    return true;
  }

  if (isConst(id_b) && a_val + diff > b_val) {
    // we must be in a conflict since a has the minimum value that
    // satisifes the constraints
    std::vector<ReasonId> conflict;
    conflict.push_back(id_reason);
    computeExplanation(UndefinedTermId, id_a, conflict);
    Debug("bv-inequality") << "InequalityGraph::addInequality conflict: constant UB \n"; 
    setConflict(conflict);
    return false; 
  }
  
  // add the inequality edge
  addEdge(id_a, id_b, strict, id_reason);
  BFSQueue queue;
  queue.push(PQueueElement(id_a, getValue(id_a), getValue(id_a), 
                           (hasExplanation(id_a) ? getExplanation(id_a) : Explanation())));
  TermIdSet seen; 
  return computeValuesBFS(queue, id_a, seen); 
}

bool InequalityGraph::updateValue(const PQueueElement& el, TermId start, const TermIdSet& seen, bool& changed) {
  TermId id = el.id;
  const BitVector& lower_bound = el.lower_bound; 
  InequalityNode& ineqNode = getInequalityNode(id);
                               
  if (ineqNode.isConstant()) {
    if (ineqNode.getValue() < lower_bound) {
      Debug("bv-inequality") << "Conflict: constant " << ineqNode.getValue() << "\n"; 
      std::vector<ReasonId> conflict;
      TermId parent = el.explanation.parent; 
      ReasonId reason = el.explanation.reason; 
      conflict.push_back(reason); 
      computeExplanation(UndefinedTermId, parent, conflict);
      Debug("bv-inequality") << "InequalityGraph::addInequality conflict: constant\n"; 
      setConflict(conflict); 
      return false; 
    }
  } else {
    // if not constant we can update the value
    if (ineqNode.getValue() < lower_bound) {
      // if we are updating the term we started with we must be in a cycle
      if (seen.count(id) && id == start) {
        TermId parent = el.explanation.parent;
        ReasonId reason = el.explanation.reason;
        std::vector<TermId> conflict;
        conflict.push_back(reason);
        computeExplanation(id, parent, conflict);
        Debug("bv-inequality") << "InequalityGraph::addInequality conflict: cycle \n"; 
        setConflict(conflict); 
        return false; 
      }
      Debug("bv-inequality-internal") << "Updating " << getTermNode(id) 
                                      << "  from " << ineqNode.getValue() << "\n"
                                      << "  to " << lower_bound << "\n";
      changed = true; 
      ineqNode.setValue(lower_bound);
      setExplanation(id, el.explanation); 
    }
  }
  return true; 
}

bool InequalityGraph::computeValuesBFS(BFSQueue& queue, TermId start, TermIdSet& seen) {
  if (queue.empty())
    return true;

  const PQueueElement current = queue.top();
  queue.pop();
  Debug("bv-inequality-internal") << "InequalityGraph::computeValuesBFS proceessing " << getTermNode(current.id) << " " << current.toString() << "\n";
  bool updated_current = false; 
  if (!updateValue(current, start, seen, updated_current)) {
    return false; 
  }
  if (seen.count(current.id) && current.id == start) {
    // we know what we didn't update start or we would have had a conflict 
    Debug("bv-inequality-internal") << "InequalityGraph::computeValuesBFS equal cycle."; 
    // this means we are in a cycle where all the values are forced to be equal
    // TODO: make sure we collapse this cycle into one big node. 
    return computeValuesBFS(queue, start, seen); 
  }
  
  if (!updated_current && !(seen.count(current.id) == 0 && current.id == start)) {
    // if we didn't update current we don't need to readd to the queue it's children 
    seen.insert(current.id);
    Debug("bv-inequality-internal") << "  unchanged " << getTermNode(current.id) << "\n";  
    return computeValuesBFS(queue, start, seen); 
  }
  
  seen.insert(current.id);
  
  const BitVector& current_value = getValue(current.id);
  
  unsigned size = getBitwidth(current.id);
  const BitVector zero(size, 0u); 
  const BitVector one(size, 1u); 
  
  const Edges& edges = getEdges(current.id);
  for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
    TermId next = it->next;
    const BitVector increment = it->strict ? one : zero; 
    const BitVector& next_lower_bound = current_value + increment;
    if (next_lower_bound < current_value) {
      // it means we have an overflow and hence a conflict
        std::vector<TermId> conflict;
        conflict.push_back(it->reason);
        computeExplanation(start, current.id, conflict);
        Debug("bv-inequality") << "InequalityGraph::addInequality conflict: cycle \n"; 
        setConflict(conflict); 
        return false; 
    }
    const BitVector& value = getValue(next); 
    PQueueElement el = PQueueElement(next, value, next_lower_bound, Explanation(current.id, it->reason)); 
    queue.push(el);
    Debug("bv-inequality-internal") << "   enqueue " << getTermNode(el.id) << " " << el.toString() << "\n"; 
  }
  return computeValuesBFS(queue, start, seen); 
}

void InequalityGraph::computeExplanation(TermId from, TermId to, std::vector<ReasonId>& explanation) {
  while(hasExplanation(to) && from != to) {
    const Explanation& exp = getExplanation(to);
    Assert (exp.reason != UndefinedReasonId); 
    explanation.push_back(exp.reason);
    
    Assert (exp.parent != UndefinedTermId); 
    to = exp.parent; 
  }
}

void InequalityGraph::addEdge(TermId a, TermId b, bool strict, TermId reason) {
  Edges& edges = getEdges(a);
  edges.push_back(InequalityEdge(b, strict, reason));
}

TermId InequalityGraph::registerTerm(TNode term) {
  if (d_termNodeToIdMap.find(term) != d_termNodeToIdMap.end()) {
    return d_termNodeToIdMap[term]; 
  }

  // store in node mapping
  TermId id = d_termNodes.size();
  Debug("bv-inequality-internal") << "InequalityGraph::registerTerm " << term << " => id"<< id << "\n"; 
  
  d_termNodes.push_back(term);
  d_termNodeToIdMap[term] = id;
  
  // create InequalityNode
  unsigned size = utils::getSize(term);
  bool isConst = term.getKind() == kind::CONST_BITVECTOR;
  BitVector value = isConst? term.getConst<BitVector>() : minValue(size); 
  
  InequalityNode ineq = InequalityNode(id, size, isConst, value);
  Assert (d_ineqNodes.size() == id); 
  d_ineqNodes.push_back(ineq);
  
  Assert (d_ineqEdges.size() == id); 
  d_ineqEdges.push_back(Edges());

  // add the default edges min <= term <= max
  addEdge(getMinValueId(size), id, false, AxiomReasonId);
  addEdge(id, getMaxValueId(size), false, AxiomReasonId); 
  
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

TNode InequalityGraph::getReasonNode(ReasonId id) const {
  Assert (d_reasonNodes.size() > id);
  return d_reasonNodes[id]; 
}

TNode InequalityGraph::getTermNode(TermId id) const {
  Assert (d_termNodes.size() > id);
  return d_termNodes[id]; 
}

void InequalityGraph::setConflict(const std::vector<ReasonId>& conflict) {
  Assert (!d_inConflict); 
  d_inConflict = true;
  d_conflict.clear(); 
  for (unsigned i = 0; i < conflict.size(); ++i) {
    if (conflict[i] != AxiomReasonId) {
      d_conflict.push_back(getReasonNode(conflict[i]));
    }
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

std::string InequalityGraph::PQueueElement::toString() const {
  ostringstream os;
  os << "(id: " << id <<", value: " << value.toString(10) << ", lower_bound: " << lower_bound.toString(10) <<")"; 
  return os.str(); 
}


// bool InequalityGraph::initializeValues(TNode a, TNode b, bool strict, TermId reason_id) {
//   TermId id_a = registerTerm(a);
//   TermId id_b = registerTerm(b);
  
//   InequalityNode& ineq_a = getInequalityNode(id_a);
//   InequalityNode& ineq_b = getInequalityNode(id_b);
  
//   unsigned size = utils::getSize(a);
//   BitVector one = mkOne(size);
//   BitVector zero = mkZero(size); 
//   BitVector diff = strict? one : zero; 
    
//   // FIXME: dumb case splitting 
//   if (ineq_a.isConstant() && ineq_b.isConstant()) {
//     Assert (a.getConst<BitVector>() + diff <= b.getConst<BitVector>());
//     ineq_a.setValue(a.getConst<BitVector>());
//     ineq_b.setValue(b.getConst<BitVector>());
//     return true; 
//   }
  
//   if (ineq_a.isConstant()) {
//     ineq_a.setValue(a.getConst<BitVector>());
//   }
  
//   if (ineq_b.isConstant()) {
//     const BitVector& const_val = b.getConst<BitVector>(); 
//     ineq_b.setValue(const_val);

//     if (hasValue(id_a) && !(ineq_a.getValue() + diff <= const_val)) {
//       // must be a conflict because we have as an invariant that a will have the min
//       // possible value for a. 
//       std::vector<ReasonId> conflict;
//       conflict.push_back(reason_id);
//       // FIXME: this will not compute the most precise conflict
//       // could be fixed by giving computeExplanation a bound (i.e. the size of const_val)
//       computeExplanation(UndefinedTermId, id_a, conflict);
//       setConflict(conflict); 
//       return false; 
//     }
//   }

//   if (!hasValue(id_a) && !hasValue(id_b)) {
//     // initialize to the minimum possible values
//     if (strict) {
//       ineq_a.setValue(MinValue(size)); 
//       ineq_b.setValue(MinValue(size) + one);
//     } else {
//       ineq_a.setValue(MinValue(size));
//       ineq_b.setValue(MinValue(size)); 
//     }
//   }
//   else if (!hasValue(id_a) && hasValue(id_b)) {
//     const BitVector& b_value = ineq_b.getValue();
//     if (strict && b_value == MinValue(size) && ineq_b.isConstant()) {
//       Debug("bv-inequality") << "Conflict: underflow " << getTerm(id_a) <<"\n";
//       std::vector<ReasonId> conflict;
//       conflict.push_back(reason_id);
//       setConflict(conflict); 
//       return false; 
//     }
//     // otherwise we attempt to increment b
//     ineq_b.setValue(one); 
//   }
//     // if a has no value then we can assign it to whatever we want
//     // to maintain the invariant that each value has the lowest value
//     // we assign it to zero 
//     ineq_a.setValue(zero); 
//   } else if (hasValue(id_a) && !hasValue(id_b)) {
//     const BitVector& a_value = ineq_a.getValue();
//     if (a_value + one < a_value) {
//       return false; 
//     }
//     ineq_b.setValue(a_value + one); 
//   }
//   return true; 
// }

// bool InequalityGraph::canReach(TermId from, TermId to) {
//   if (from == to )
//     return true;
  
//   TermIdSet seen;
//   TermIdQueue queue;
//   queue.push(from); 
//   bfs(seen, queue);
//   if (seen.count(to)) {
//     return true; 
//   }
//   return false; 
// }

// void InequalityGraph::bfs(TermIdSet& seen, TermIdQueue& queue) {
//   if (queue.empty())
//     return;
  
//   TermId current = queue.front();
//   queue.pop();

//   const Edges& edges = getOutEdges(current);
//   for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
//     TermId next = it->next;
//     if(seen.count(next) == 0) {
//       seen.insert(next);
//       queue.push(next); 
//     }
//   }
//   bfs(seen, queue);
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

// TermId InequalityGraph::getMaxParent(TermId id) {
//   const Edges& in_edges = getInEdges(id);
//   Assert (in_edges.size() != 0);
  
//   BitVector max(getBitwidth(0), 0u);
//   TermId max_id = UndefinedTermId; 
//   for (Edges::const_iterator it = in_edges.begin(); it!= in_edges.end(); ++it) {
//     // Assert (seen.count(it->next));
//     const BitVector& value = getInequalityNode(it->next).getValue();
//     if (value >= max) {
//       max = value;
//       max_id = it->next; 
//     }
//   }
//   Assert (max_id != UndefinedTermId); 
//   return max_id; 
// }
