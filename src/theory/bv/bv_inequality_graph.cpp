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


// BitVector InequalityGraph::maxValue(unsigned bitwidth) {
//   if (d_signed) {
//     return BitVector(1, 0u).concat(~BitVector(bitwidth - 1, 0u)); 
//   }
//   return ~BitVector(bitwidth, 0u);
// }

// BitVector InequalityGraph::minValue(unsigned bitwidth) {
//   if (d_signed) {
//     return ~BitVector(bitwidth, 0u); 
//   } 
//   return BitVector(bitwidth, 0u);
// }

// TermId InequalityGraph::getMaxValueId(unsigned bitwidth) {
//   BitVector bv = maxValue(bitwidth); 
//   Node max = utils::mkConst(bv); 
  
//   if (d_termNodeToIdMap.find(max) == d_termNodeToIdMap.end()) {
//     TermId id = d_termNodes.size(); 
//     d_termNodes.push_back(max);
//     d_termNodeToIdMap[max] = id;
//     InequalityNode node(id, bitwidth, true, bv);
//     d_ineqNodes.push_back(node); 

//     // although it will never have out edges we need this to keep the size of
//     // d_termNodes and d_ineqEdges in sync
//     d_ineqEdges.push_back(Edges());
//     return id; 
//   }
//   return d_termNodeToIdMap[max]; 
// }

// TermId InequalityGraph::getMinValueId(unsigned bitwidth) {
//   BitVector bv = minValue(bitwidth); 
//   Node min = utils::mkConst(bv); 

//   if (d_termNodeToIdMap.find(min) == d_termNodeToIdMap.end()) {
//     TermId id = d_termNodes.size(); 
//     d_termNodes.push_back(min);
//     d_termNodeToIdMap[min] = id;
//     d_ineqEdges.push_back(Edges());
//     InequalityNode node = InequalityNode(id, bitwidth, true, bv);
//     d_ineqNodes.push_back(node); 
//     return id; 
//   }
//   return d_termNodeToIdMap[min]; 
// }

bool InequalityGraph::addInequality(TNode a, TNode b, bool strict, TNode reason) {
  Debug("bv-inequality") << "InequlityGraph::addInequality " << a << " " << b << " strict: " << strict << "\n"; 

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
  ModelValue mv = hasModelValue(id_a) ? getModelValue(id_a) : ModelValue();
  queue.push(PQueueElement(id_a,  getValue(id_a), mv));
  TermIdSet seen; 
  return computeValuesBFS(queue, id_a, seen); 
}

bool InequalityGraph::updateValue(const PQueueElement& el, TermId start, const TermIdSet& seen, bool& changed) {
  TermId id = el.id;
  const BitVector& lower_bound = el.lower_bound; 
  InequalityNode& ineqNode = getInequalityNode(id);
                               
  if (ineqNode.isConstant()) {
    if (getValue(id) < lower_bound) {
      Debug("bv-inequality") << "Conflict: constant " << getValue(id) << "\n"; 
      std::vector<ReasonId> conflict;
      TermId parent = el.model_value.parent; 
      ReasonId reason = el.model_value.reason; 
      conflict.push_back(reason); 
      computeExplanation(UndefinedTermId, parent, conflict);
      Debug("bv-inequality") << "InequalityGraph::addInequality conflict: constant\n"; 
      setConflict(conflict); 
      return false; 
    }
  } else {
    // if not constant we can update the value
    if (getValue(id) < lower_bound) {
      // if we are updating the term we started with we must be in a cycle
      if (seen.count(id) && id == start) {
        TermId parent = el.model_value.parent;
        ReasonId reason = el.model_value.reason;
        std::vector<TermId> conflict;
        conflict.push_back(reason);
        computeExplanation(id, parent, conflict);
        Debug("bv-inequality") << "InequalityGraph::addInequality conflict: cycle \n"; 
        setConflict(conflict); 
        return false; 
      }
      Debug("bv-inequality-internal") << "Updating " << getTermNode(id) 
                                      << "  from " << getValue(id) << "\n"
                                      << "  to " << lower_bound << "\n";
      changed = true;
      ModelValue mv = el.model_value;
      mv.value = lower_bound; 
      setModelValue(id, mv); 
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
    PQueueElement el = PQueueElement(next, next_lower_bound, ModelValue(value, current.id, it->reason)); 
    queue.push(el);
    Debug("bv-inequality-internal") << "   enqueue " << getTermNode(el.id) << " " << el.toString() << "\n"; 
  }
  return computeValuesBFS(queue, start, seen); 
}

void InequalityGraph::computeExplanation(TermId from, TermId to, std::vector<ReasonId>& explanation) {
  if(Debug.isOn("bv-inequality")) {
    if (from == UndefinedTermId) {
      Debug("bv-inequality") << "InequalityGraph::computeExplanation " << getTermNode(to) << "\n";
    } else {
      Debug("bv-inequality") << "InequalityGraph::computeExplanation " << getTermNode(from) <<" => "
                             << getTermNode(to) << "\n";
    }
  }

  TermIdSet seen;

  while(hasReason(to) && from != to && !seen.count(to)) {
    seen.insert(to); 
    const ModelValue& exp = getModelValue(to);
    Assert (exp.reason != UndefinedReasonId); 
    explanation.push_back(exp.reason);
    Assert (exp.parent != UndefinedTermId); 
    to = exp.parent; 
    Debug("bv-inequality-internal") << "  parent: " << getTermNode(to) << "\n"
                                    << "  reason: " << getReasonNode(exp.reason) << "\n"; 
  }
}

void InequalityGraph::addEdge(TermId a, TermId b, bool strict, TermId reason) {
  Debug("bv-inequality-internal") << "InequalityGraph::addEdge " << getTermNode(a) << " => " << getTermNode(b) << "\n"
                                  << " strict ? " << strict << "\n"; 
  Edges& edges = getEdges(a);
  InequalityEdge new_edge(b, strict, reason); 
  edges.push_back(new_edge);
  d_undoStack.push_back(std::make_pair(a, new_edge));
  d_undoStackIndex = d_undoStackIndex + 1; 
}

void InequalityGraph::initializeModelValue(TNode node) {
  TermId id = getTermId(node); 
  Assert (!hasModelValue(id));
  bool isConst = node.getKind() == kind::CONST_BITVECTOR;
  unsigned size = utils::getSize(node); 
  BitVector value = isConst? node.getConst<BitVector>() : BitVector(size, 0u); 
  setModelValue(id, ModelValue(value, UndefinedTermId, UndefinedReasonId));
}

bool InequalityGraph::isRegistered(TNode term) const {
  return d_termNodeToIdMap.find(term) != d_termNodeToIdMap.end(); 
}

TermId InequalityGraph::registerTerm(TNode term) {
  if (d_termNodeToIdMap.find(term) != d_termNodeToIdMap.end()) {
    TermId id = d_termNodeToIdMap[term];
    if (!hasModelValue(id)) {
      // we could have backtracked and
      initializeModelValue(term); 
    }
    return id; 
  }

  // store in node mapping
  TermId id = d_termNodes.size();
  Debug("bv-inequality-internal") << "InequalityGraph::registerTerm " << term << " => id"<< id << "\n"; 
  
  d_termNodes.push_back(term);
  d_termNodeToIdMap[term] = id;
  
  // create InequalityNode
  unsigned size = utils::getSize(term);

  bool isConst = term.getKind() == kind::CONST_BITVECTOR;
  InequalityNode ineq = InequalityNode(id, size, isConst);

  Assert (d_ineqNodes.size() == id); 
  d_ineqNodes.push_back(ineq);
  
  Assert (d_ineqEdges.size() == id); 
  d_ineqEdges.push_back(Edges());

  initializeModelValue(term); 
  
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

TermId InequalityGraph::getTermId(TNode node) const {
  Assert (d_termNodeToIdMap.find(node) != d_termNodeToIdMap.end());
  return d_termNodeToIdMap.find(node)->second; 
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

void InequalityGraph::setModelValue(TermId term, const ModelValue& mv) {
  d_modelValues[term] = mv; 
}

InequalityGraph::ModelValue InequalityGraph::getModelValue(TermId term) const {
  Assert (d_modelValues.find(term) != d_modelValues.end());
  return (*(d_modelValues.find(term))).second; 
}

bool InequalityGraph::hasModelValue(TermId id) const {
  return d_modelValues.find(id) != d_modelValues.end(); 
}

BitVector InequalityGraph::getValue(TermId id) const {
  Assert (hasModelValue(id)); 
  BitVector res = (*(d_modelValues.find(id))).second.value;
  return res; 
}

bool InequalityGraph::hasReason(TermId id) const {
  const ModelValue& mv = getModelValue(id);
  return mv.reason != UndefinedReasonId; 
}

bool InequalityGraph::addDisequality(TNode a, TNode b, TNode reason) {
  Debug("bv-inequality") << "InequalityGraph::addDisequality " << reason << "\n"; 
  d_disequalities.push_back(reason);

  if (!isRegistered(a) || !isRegistered(b)) {
    splitDisequality(reason);
    return true; 
  }
  TermId id_a = getTermId(a);
  TermId id_b = getTermId(b);
  if (!hasModelValue(id_a)) {
    initializeModelValue(a); 
  }
  if (!hasModelValue(id_b)) {
    initializeModelValue(b); 
  }
  const BitVector& val_a = getValue(id_a);
  const BitVector& val_b = getValue(id_b);
  if (val_a == val_b) {
    if (a.getKind() == kind::CONST_BITVECTOR) {
      // then we know b cannot be smaller  than the assigned value so we try to make it larger
      return addInequality(a, b, true, reason);
    }
    if (b.getKind() == kind::CONST_BITVECTOR) {
      return addInequality(b, a, true, reason);
    }
    // if none of the terms are constants just add the lemma 
    splitDisequality(reason);
  } else {
    Debug("bv-inequality-internal") << "Disequal: " << a << " => " << val_a.toString(10) << "\n"
                                    << "          " << b << " => " << val_b.toString(10) << "\n"; 
  }
  return true; 
}

void InequalityGraph::splitDisequality(TNode diseq) {
  Debug("bv-inequality-internal")<<"InequalityGraph::splitDisequality " << diseq <<"\n"; 
  Assert (diseq.getKind() == kind::NOT && diseq[0].getKind() == kind::EQUAL);
  TNode a = diseq[0][0];
  TNode b = diseq[0][1];
  Node a_lt_b = utils::mkNode(kind::BITVECTOR_ULT, a, b);
  Node b_lt_a = utils::mkNode(kind::BITVECTOR_ULT, b, a);
  Node split = utils::mkNode(kind::OR, a_lt_b, b_lt_a);
  Node lemma = utils::mkNode(kind::IMPLIES, diseq, split);
  if (d_lemmasAdded.find(lemma) == d_lemmasAdded.end()) { 
    d_lemmaQueue.push_back(lemma);
  }
}

void InequalityGraph::getNewLemmas(std::vector<TNode>& new_lemmas) {
  for (unsigned i = d_lemmaIndex; i < d_lemmaQueue.size(); ++i)  {
    TNode lemma = d_lemmaQueue[i];
    if (d_lemmasAdded.find(lemma) == d_lemmasAdded.end()) {
      new_lemmas.push_back(lemma);
      d_lemmasAdded.insert(lemma); 
    }
    d_lemmaIndex = d_lemmaIndex + 1; 
  } 
}

std::string InequalityGraph::PQueueElement::toString() const {
  ostringstream os;
  os << "(id: " << id << ", lower_bound: " << lower_bound.toString(10) <<", old_value: " << model_value.value.toString(10) << ")"; 
  return os.str(); 
}

void InequalityGraph::backtrack() {
  Debug("bv-inequality-internal") << "InequalityGraph::backtrack()\n"; 
  int size = d_undoStack.size(); 
  for (int i = size - 1; i >= (int)d_undoStackIndex.get(); --i) {
    Assert (!d_undoStack.empty());
    TermId id = d_undoStack.back().first; 
    InequalityEdge edge = d_undoStack.back().second;
    d_undoStack.pop_back();
    
    Debug("bv-inequality-internal") << " remove edge " << getTermNode(id) << " => "
                                                       << getTermNode(edge.next) <<"\n"; 
    Edges& edges = getEdges(id);
    for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
      Debug("bv-inequality-internal") << getTermNode(it->next) <<" " << it->strict << "\n"; 
    }
    Assert (!edges.empty());
    InequalityEdge back = edges.back(); 
    Assert (back == edge);
    edges.pop_back(); 
  }
}
