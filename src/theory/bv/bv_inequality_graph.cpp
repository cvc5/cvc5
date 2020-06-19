/*********************                                                        */
/*! \file bv_inequality_graph.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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


bool InequalityGraph::addInequality(TNode a, TNode b, bool strict, TNode reason) {
  Debug("bv-inequality") << "InequalityGraph::addInequality " << a << " " << b << " strict: " << strict << "\n"; 

  TermId id_a = registerTerm(a);
  TermId id_b = registerTerm(b);
  ReasonId id_reason = registerReason(reason);

  Assert(!(isConst(id_a) && isConst(id_b)));
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
  BFSQueue queue(&d_modelValues);
  Assert(hasModelValue(id_a));
  queue.push(id_a);
  return processQueue(queue, id_a); 
}

bool InequalityGraph::updateValue(TermId id, ModelValue new_mv, TermId start, bool& changed) {
  BitVector lower_bound = new_mv.value;
  
  if (isConst(id)) {
    if (getValue(id) < lower_bound) {
      Debug("bv-inequality") << "Conflict: constant " << getValue(id) << "\n"; 
      std::vector<ReasonId> conflict;
      TermId parent = new_mv.parent; 
      ReasonId reason = new_mv.reason; 
      conflict.push_back(reason); 
      computeExplanation(UndefinedTermId, parent, conflict);
      Debug("bv-inequality") << "InequalityGraph::addInequality conflict: constant\n"; 
      setConflict(conflict); 
      return false; 
    }
  } else {
    // if not constant we can try to update the value
    if (getValue(id) < lower_bound) {
      // if we are updating the term we started with we must be in a cycle
      if (id == start) {
        TermId parent = new_mv.parent;
        ReasonId reason = new_mv.reason;
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
      setModelValue(id, new_mv); 
    }
  }
  return true; 
}

bool InequalityGraph::processQueue(BFSQueue& queue, TermId start) {
  while (!queue.empty()) {
    TermId current = queue.top();
    queue.pop();
    Debug("bv-inequality-internal") << "InequalityGraph::processQueue processing " << getTermNode(current) << "\n";
  
    BitVector current_value = getValue(current);
  
    unsigned size = getBitwidth(current);
    const BitVector zero(size, 0u); 
    const BitVector one(size, 1u); 
  
    const Edges& edges = getEdges(current);
    for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
      TermId next = it->next;
      ReasonId reason = it->reason;

      const BitVector increment = it->strict ? one : zero; 
      const BitVector next_lower_bound = current_value + increment;

      if (next_lower_bound < current_value) {
        // it means we have an overflow and hence a conflict
        std::vector<TermId> conflict;
        conflict.push_back(it->reason);
        Assert(hasModelValue(start));
        ReasonId start_reason = getModelValue(start).reason;
        if (start_reason != UndefinedReasonId) {
          conflict.push_back(start_reason);
        }
        computeExplanation(UndefinedTermId, current, conflict);
        Debug("bv-inequality") << "InequalityGraph::addInequality conflict: cycle \n"; 
        setConflict(conflict); 
        return false; 
      }
      
      ModelValue new_mv(next_lower_bound, current, reason);       
      bool updated = false; 
      if (!updateValue(next, new_mv, start, updated)) {
        return false; 
      }
      
      if (next == start) {
        // we know what we didn't update start or we would have had a conflict 
        // this means we are in a cycle where all the values are forced to be equal
        Debug("bv-inequality-internal") << "InequalityGraph::processQueue equal cycle."; 
        continue; 
      }
      
      if (!updated) {
        // if we didn't update current we don't need to add to the queue it's children 
        Debug("bv-inequality-internal") << "  unchanged " << getTermNode(next) << "\n";  
        continue; 
      }

      queue.push(next);
      Debug("bv-inequality-internal") << "   enqueue " << getTermNode(next) << "\n"; 
    }
  }
  return true; 
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
    Assert(exp.reason != UndefinedReasonId);
    explanation.push_back(exp.reason);
    Assert(exp.parent != UndefinedTermId);
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
  Assert(!hasModelValue(id));
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

  Assert(d_ineqNodes.size() == id);
  d_ineqNodes.push_back(ineq);

  Assert(d_ineqEdges.size() == id);
  d_ineqEdges.push_back(Edges());

  initializeModelValue(term); 
  
  return id; 
}

ReasonId InequalityGraph::registerReason(TNode reason) {
  if (d_reasonToIdMap.find(reason) != d_reasonToIdMap.end()) {
    return d_reasonToIdMap[reason]; 
  }
  d_reasonSet.insert(reason);
  ReasonId id = d_reasonNodes.size();
  d_reasonNodes.push_back(reason);
  d_reasonToIdMap[reason] = id;
  Debug("bv-inequality-internal") << "InequalityGraph::registerReason " << reason << " => id"<< id << "\n"; 
  return id; 
}

TNode InequalityGraph::getReasonNode(ReasonId id) const {
  Assert(d_reasonNodes.size() > id);
  return d_reasonNodes[id]; 
}

TNode InequalityGraph::getTermNode(TermId id) const {
  Assert(d_termNodes.size() > id);
  return d_termNodes[id]; 
}

TermId InequalityGraph::getTermId(TNode node) const {
  Assert(d_termNodeToIdMap.find(node) != d_termNodeToIdMap.end());
  return d_termNodeToIdMap.find(node)->second; 
}

void InequalityGraph::setConflict(const std::vector<ReasonId>& conflict) {
  Assert(!d_inConflict);
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
  Assert(d_modelValues.find(term) != d_modelValues.end());
  return (*(d_modelValues.find(term))).second; 
}

bool InequalityGraph::hasModelValue(TermId id) const {
  return d_modelValues.find(id) != d_modelValues.end(); 
}

BitVector InequalityGraph::getValue(TermId id) const {
  Assert(hasModelValue(id));
  return (*(d_modelValues.find(id))).second.value;
}

bool InequalityGraph::hasReason(TermId id) const {
  const ModelValue& mv = getModelValue(id);
  return mv.reason != UndefinedReasonId; 
}

bool InequalityGraph::addDisequality(TNode a, TNode b, TNode reason) {
  Debug("bv-inequality") << "InequalityGraph::addDisequality " << reason << "\n"; 
  d_disequalities.push_back(reason);

  if (!isRegistered(a) || !isRegistered(b)) {
    //splitDisequality(reason);
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
  const BitVector val_a = getValue(id_a);
  const BitVector val_b = getValue(id_b);
  if (val_a == val_b) {
    if (a.getKind() == kind::CONST_BITVECTOR) {
      // then we know b cannot be smaller  than the assigned value so we try to make it larger
      std::vector<ReasonId> explanation_ids; 
      computeExplanation(UndefinedTermId, id_b, explanation_ids); 
      std::vector<TNode> explanation_nodes;
      explanation_nodes.push_back(reason);
      for (unsigned i = 0; i < explanation_ids.size(); ++i) {
        explanation_nodes.push_back(getReasonNode(explanation_ids[i])); 
      }
      Node explanation = utils::mkAnd(explanation_nodes);
      d_reasonSet.insert(explanation); 
      return addInequality(a, b, true, explanation);
    }
    if (b.getKind() == kind::CONST_BITVECTOR) {
      // then we know b cannot be smaller  than the assigned value so we try to make it larger
      std::vector<ReasonId> explanation_ids; 
      computeExplanation(UndefinedTermId, id_a, explanation_ids); 
      std::vector<TNode> explanation_nodes;
      explanation_nodes.push_back(reason);
      for (unsigned i = 0; i < explanation_ids.size(); ++i) {
        explanation_nodes.push_back(getReasonNode(explanation_ids[i])); 
      }
      Node explanation = utils::mkAnd(explanation_nodes);
      d_reasonSet.insert(explanation); 
      return addInequality(b, a, true, explanation);
    }
    // if none of the terms are constants just add the lemma 
    //splitDisequality(reason);
  } else {
    Debug("bv-inequality-internal") << "Disequal: " << a << " => " << val_a.toString(10) << "\n"
                                    << "          " << b << " => " << val_b.toString(10) << "\n"; 
  }
  return true; 
}

// void InequalityGraph::splitDisequality(TNode diseq) {
//   Debug("bv-inequality-internal")<<"InequalityGraph::splitDisequality " <<
//   diseq <<"\n"; Assert (diseq.getKind() == kind::NOT &&
//   diseq[0].getKind() == kind::EQUAL); if
//   (d_disequalitiesAlreadySplit.find(diseq) ==
//   d_disequalitiesAlreadySplit.end()) {
//     d_disequalitiesToSplit.push_back(diseq);
//   }
// }

void InequalityGraph::backtrack() {
  Debug("bv-inequality-internal") << "InequalityGraph::backtrack()\n"; 
  int size = d_undoStack.size(); 
  for (int i = size - 1; i >= (int)d_undoStackIndex.get(); --i) {
    Assert(!d_undoStack.empty());
    TermId id = d_undoStack.back().first; 
    InequalityEdge edge = d_undoStack.back().second;
    d_undoStack.pop_back();
    
    Debug("bv-inequality-internal") << " remove edge " << getTermNode(id) << " => "
                                                       << getTermNode(edge.next) <<"\n"; 
    Edges& edges = getEdges(id);
    for (Edges::const_iterator it = edges.begin(); it!= edges.end(); ++it) {
      Debug("bv-inequality-internal") << getTermNode(it->next) <<" " << it->strict << "\n"; 
    }
    Assert(!edges.empty());
    Assert(edges.back() == edge);
    edges.pop_back(); 
  }
}

Node InequalityGraph::makeDiseqSplitLemma(TNode diseq)
{
  Assert(diseq.getKind() == kind::NOT && diseq[0].getKind() == kind::EQUAL);
  NodeManager* nm = NodeManager::currentNM();
  TNode a = diseq[0][0];
  TNode b = diseq[0][1];
  Node a_lt_b = nm->mkNode(kind::BITVECTOR_ULT, a, b);
  Node b_lt_a = nm->mkNode(kind::BITVECTOR_ULT, b, a);
  Node eq = diseq[0];
  Node lemma = nm->mkNode(kind::OR, a_lt_b, b_lt_a, eq);
  return lemma;
}

void InequalityGraph::checkDisequalities(std::vector<Node>& lemmas) {
  for (CDQueue<TNode>::const_iterator it = d_disequalities.begin(); it != d_disequalities.end(); ++it) {
    if (d_disequalitiesAlreadySplit.find(*it) == d_disequalitiesAlreadySplit.end()) {
      // if we haven't already split on this disequality
      TNode diseq = *it;
      TermId a_id = registerTerm(diseq[0][0]);
      TermId b_id = registerTerm(diseq[0][1]);
      if (getValue(a_id) == getValue(b_id)) {
        lemmas.push_back(makeDiseqSplitLemma(diseq));
        d_disequalitiesAlreadySplit.insert(diseq);
      }
    }
  }
}

bool InequalityGraph::isLessThan(TNode a, TNode b) {
  Assert(isRegistered(a) && isRegistered(b));
  Unimplemented(); 
}

bool InequalityGraph::hasValueInModel(TNode node) const {
  if (isRegistered(node)) {
    TermId id = getTermId(node);
    return hasModelValue(id); 
  }
  return false; 
}

BitVector InequalityGraph::getValueInModel(TNode node) const {
  TermId id = getTermId(node);
  Assert(hasModelValue(id));
  return getValue(id); 
}

void InequalityGraph::getAllValuesInModel(std::vector<Node>& assignments)
{
  NodeManager* nm = NodeManager::currentNM();
  for (ModelValues::const_iterator it = d_modelValues.begin();
       it != d_modelValues.end();
       ++it)
  {
    TermId id = (*it).first;
    BitVector value = (*it).second.value;
    TNode var = getTermNode(id);
    Node constant = utils::mkConst(value);
    Node assignment = nm->mkNode(kind::EQUAL, var, constant);
    assignments.push_back(assignment);
    Debug("bitvector-model") << "   " << var << " => " << constant << "\n";
  }
}
