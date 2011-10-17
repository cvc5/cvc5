/*********************                                                        */
/*! \file equality_engine_impl.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

#include "cvc4_private.h"

#pragma once

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace uf {

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::enqueue(const MergeCandidate& candidate) {
    Debug("equality") << "EqualityEngine::enqueue(" << candidate.toString(*this) << ")" << std::endl;
    d_propagationQueue.push(candidate);
}

template <typename NotifyClass>
EqualityNodeId EqualityEngine<NotifyClass>::newApplicationNode(TNode original, EqualityNodeId t1, EqualityNodeId t2) {
  Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ")" << std::endl;

  ++ d_stats.functionTermsCount;

  // Get another id for this
  EqualityNodeId funId = newNode(original, true);
    // The function application we're creating
  EqualityNodeId t1ClassId = getEqualityNode(t1).getFind();
  EqualityNodeId t2ClassId = getEqualityNode(t2).getFind();
  FunctionApplication funNormalized(t1ClassId, t2ClassId);

  // We add the normalized version, the term needs to be re-added on each backtrack
  d_applications[funId] = funNormalized;

  // Add the lookup data, if it's not already there
  typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
  if (find == d_applicationLookup.end()) {
    // When we backtrack, if the lookup is not there anymore, we'll add it again
    Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): no lookup, setting up" << std::endl;
    // Mark the normalization to the lookup
    d_applicationLookup[funNormalized] = funId;
  } else {
    // If it's there, we need to merge these two
    Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): lookup exists, adding to queue" << std::endl;
    enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
    propagate();
  }

  // Add to the use lists
  d_equalityNodes[t1ClassId].usedIn(funId, d_useListNodes);
  d_equalityNodes[t2ClassId].usedIn(funId, d_useListNodes);

  // Return the new id
  Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ") => " << funId << std::endl;

  return funId;
}

template <typename NotifyClass>
EqualityNodeId EqualityEngine<NotifyClass>::newNode(TNode node, bool isApplication) {

  Debug("equality") << "EqualityEngine::newNode(" << node << ", " << (isApplication ? "function" : "regular") << ")" << std::endl;

  ++ d_stats.termsCount;

  // Register the new id of the term
  EqualityNodeId newId = d_nodes.size();
  d_nodeIds[node] = newId;
  // Add the node to it's position
  d_nodes.push_back(node);
  // Note if this is an application or not
  d_applications.push_back(FunctionApplication());
  // Add the trigger list for this node
  d_nodeTriggers.push_back(+null_trigger);
  // Add it to the equality graph
  d_equalityGraph.push_back(+null_edge);
  // Mark the no-individual trigger
  d_nodeIndividualTrigger.push_back(+null_id);
  // Add the equality node to the nodes
  d_equalityNodes.push_back(EqualityNode(newId));

  // Increase the counters
  d_nodesCount = d_nodesCount + 1;

  Debug("equality") << "EqualityEngine::newNode(" << node << ", " << (isApplication ? "function" : "regular") << ") => " << newId << std::endl;

  return newId;
}


template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addTerm(TNode t) {

  Debug("equality") << "EqualityEngine::addTerm(" << t << ")" << std::endl;

  // If there already, we're done
  if (hasTerm(t)) {
    return;
  }

  EqualityNodeId result;

  // If a function application we go in
  if (t.getNumChildren() > 0 && d_congruenceKinds[t.getKind()])
  {
    // Add the operator
    TNode tOp = t.getOperator();
    addTerm(tOp);
    // Add all the children and Curryfy
    result = getNodeId(tOp);
    for (unsigned i = 0; i < t.getNumChildren(); ++ i) {
      // Add the child
      addTerm(t[i]);
      // Add the application
      result = newApplicationNode(t, result, getNodeId(t[i]));
    }
  } else {
    // Otherwise we just create the new id
    result = newNode(t, false);
  }

  Debug("equality") << "EqualityEngine::addTerm(" << t << ") => " << result << std::endl;
}

template <typename NotifyClass>
bool EqualityEngine<NotifyClass>::hasTerm(TNode t) const {
  return d_nodeIds.find(t) != d_nodeIds.end();
}

template <typename NotifyClass>
EqualityNodeId EqualityEngine<NotifyClass>::getNodeId(TNode node) const {
  Assert(hasTerm(node), node.toString().c_str());
  return (*d_nodeIds.find(node)).second;
}

template <typename NotifyClass>
EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(TNode t) {
  return getEqualityNode(getNodeId(t));
}

template <typename NotifyClass>
EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(EqualityNodeId nodeId) {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

template <typename NotifyClass>
const EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(TNode t) const {
  return getEqualityNode(getNodeId(t));
}

template <typename NotifyClass>
const EqualityNode& EqualityEngine<NotifyClass>::getEqualityNode(EqualityNodeId nodeId) const {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addEquality(TNode t1, TNode t2, TNode reason) {

  Debug("equality") << "EqualityEngine::addEquality(" << t1 << "," << t2 << ")" << std::endl;

  // Add the terms if they are not already in the database
  addTerm(t1);
  addTerm(t2);

  // Add to the queue and propagate
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);
  enqueue(MergeCandidate(t1Id, t2Id, MERGED_THROUGH_EQUALITY, reason));
  propagate();
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addDisequality(TNode t1, TNode t2, TNode reason) {

  Debug("equality") << "EqualityEngine::addDisequality(" << t1 << "," << t2 << ")" << std::endl;

  Node equality = t1.eqNode(t2);
  addEquality(equality, d_false, reason);
}


template <typename NotifyClass>
TNode EqualityEngine<NotifyClass>::getRepresentative(TNode t) const {

  Debug("equality") << "EqualityEngine::getRepresentative(" << t << ")" << std::endl;

  Assert(hasTerm(t));

  // Both following commands are semantically const
  EqualityNodeId representativeId = getEqualityNode(t).getFind();

  Debug("equality") << "EqualityEngine::getRepresentative(" << t << ") => " << d_nodes[representativeId] << std::endl;

  return d_nodes[representativeId];
}

template <typename NotifyClass>
bool EqualityEngine<NotifyClass>::areEqual(TNode t1, TNode t2) const {
  Debug("equality") << "EqualityEngine::areEqual(" << t1 << "," << t2 << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Both following commands are semantically const
  EqualityNodeId rep1 = getEqualityNode(t1).getFind();
  EqualityNodeId rep2 = getEqualityNode(t2).getFind();

  Debug("equality") << "EqualityEngine::areEqual(" << t1 << "," << t2 << ") => " << (rep1 == rep2 ? "true" : "false") << std::endl;

  return rep1 == rep2;
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::merge(EqualityNode& class1, EqualityNode& class2, std::vector<TriggerId>& triggers) {

  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << ")" << std::endl;

  Assert(triggers.empty());

  ++ d_stats.mergesCount;

  EqualityNodeId class1Id = class1.getFind();
  EqualityNodeId class2Id = class2.getFind();

  // Update class2 representative information
  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating class " << class2Id << std::endl;
  EqualityNodeId currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): " << currentId << "->" << class1Id << std::endl;
    currentNode.setFind(class1Id);

    // Go through the triggers and inform if necessary
    TriggerId currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != null_trigger) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      Trigger& otherTrigger = d_equalityTriggers[currentTrigger ^ 1];

      // If the two are not already in the same class
      if (otherTrigger.classId != trigger.classId) {
        trigger.classId = class1Id;
        // If they became the same, call the trigger
        if (otherTrigger.classId == class1Id) {
          // Id of the real trigger is half the internal one
          triggers.push_back(currentTrigger);
        }
      }

      // Go to the next trigger
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);


  // Update class2 table lookup and information
  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of " << class2Id << std::endl;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);    
    Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of node " << currentId << std::endl;
 
    // Go through the uselist and check for congruences
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      // Get the node of the use list
      UseListNode& useNode = d_useListNodes[currentUseId];
      // Get the function application
      EqualityNodeId funId = useNode.getApplicationId();
      Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): " << currentId << " in " << d_nodes[funId] << std::endl;
      const FunctionApplication& fun = d_applications[useNode.getApplicationId()];
      // Check if there is an application with find arguments
      EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
      EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
      FunctionApplication funNormalized(aNormalized, bNormalized);
      typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
      if (find != d_applicationLookup.end()) {
        // Applications fun and the funNormalized can be merged due to congruence
        if (getEqualityNode(funId).getFind() != getEqualityNode(find->second).getFind()) {
          enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
        }
      } else {
        // There is no representative, so we can add one, we remove this when backtracking
        d_applicationLookup[funNormalized] = funId;
      }
      // Go to the next one in the use list
      currentUseId = useNode.getNext();
    }

    // Move to the next node
    currentId = currentNode.getNext();
  } while (currentId != class2Id);

  // Now merge the lists
  class1.merge<true>(class2);

  // Notfiy the triggers
  EqualityNodeId class1triggerId = d_nodeIndividualTrigger[class1Id];
  EqualityNodeId class2triggerId = d_nodeIndividualTrigger[class2Id];
  if (class2triggerId != +null_id) {
    if (class1triggerId == +null_id) {
      // If class1 is not an individual trigger, but class2 is, mark it
      d_nodeIndividualTrigger[class1Id] = class2triggerId;
      // Add it to the list for backtracking
      d_individualTriggers.push_back(class1Id);
      d_individualTriggersSize = d_individualTriggersSize + 1;  
    } else {
      // Notify when done
      if (d_performNotify) {
        d_notify.notify(d_nodes[class1triggerId], d_nodes[class2triggerId]); 
      }
    }	
  }
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::undoMerge(EqualityNode& class1, EqualityNode& class2, EqualityNodeId class2Id) {

  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << ")" << std::endl;

  // Now unmerge the lists (same as merge)
  class1.merge<false>(class2);

  // First undo the table lookup changes
  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << "): undoing lookup changes" << std::endl;
  EqualityNodeId currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Go through the uselist and check for congruences
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      // Get the node of the use list
      UseListNode& useNode = d_useListNodes[currentUseId];
      // Get the function application
      EqualityNodeId funId = useNode.getApplicationId();
      const FunctionApplication& fun = d_applications[useNode.getApplicationId()];
      // Get the application with find arguments
      EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
      EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
      FunctionApplication funNormalized(aNormalized, bNormalized);
      typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
      // If the id is the one we set, then we undo it
      if (find != d_applicationLookup.end() && find->second == funId) {
        d_applicationLookup.erase(find);
      }
      // Go to the next one in the use list
      currentUseId = useNode.getNext();
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Update class2 representative information
  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << "): undoing representative info" << std::endl;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    currentNode.setFind(class2Id);

    // Go through the trigger list (if any) and undo the class
    TriggerId currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != null_trigger) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      trigger.classId = class2Id;
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Now set any missing lookups and check for any congruences on backtrack
  std::vector<MergeCandidate> possibleCongruences;
  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << "): checking for any unset lookups" << std::endl;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Go through the uselist and check for congruences
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      // Get the node of the use list
      UseListNode& useNode = d_useListNodes[currentUseId];
      // Get the function application
      EqualityNodeId funId = useNode.getApplicationId();
      const FunctionApplication& fun = d_applications[useNode.getApplicationId()];
      // Get the application with find arguments
      EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
      EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
      FunctionApplication funNormalized(aNormalized, bNormalized);
      typename ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
      // If the id doesn't exist, we'll set it
      if (find == d_applicationLookup.end()) {
        d_applicationLookup[funNormalized] = funId;
      }
      // Go to the next one in the use list
      currentUseId = useNode.getNext();
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::backtrack() {

  // If we need to backtrack then do it
  if (d_assertedEqualitiesCount < d_assertedEqualities.size()) {

    // Clear the propagation queue
    while (!d_propagationQueue.empty()) {
      d_propagationQueue.pop();
    }

    Debug("equality") << "EqualityEngine::backtrack(): nodes" << std::endl;

    for (int i = (int)d_assertedEqualities.size() - 1, i_end = (int)d_assertedEqualitiesCount; i >= i_end; --i) {
      // Get the ids of the merged classes
      Equality& eq = d_assertedEqualities[i];
      // Undo the merge
      undoMerge(d_equalityNodes[eq.lhs], d_equalityNodes[eq.rhs], eq.rhs);
    }

    d_assertedEqualities.resize(d_assertedEqualitiesCount);

    Debug("equality") << "EqualityEngine::backtrack(): edges" << std::endl;

    for (int i = (int)d_equalityEdges.size() - 2, i_end = (int)(2*d_assertedEqualitiesCount); i >= i_end; i -= 2) {
      EqualityEdge& edge1 = d_equalityEdges[i];
      EqualityEdge& edge2 = d_equalityEdges[i | 1];
      d_equalityGraph[edge2.getNodeId()] = edge1.getNext();
      d_equalityGraph[edge1.getNodeId()] = edge2.getNext();
    }

    d_equalityEdges.resize(2 * d_assertedEqualitiesCount);
  }

  if (d_individualTriggers.size() > d_individualTriggersSize) {
    // Unset the individual triggers
    for (int i = d_individualTriggers.size() - 1, i_end = d_individualTriggersSize; i >= i_end; -- i) {
      d_nodeIndividualTrigger[d_individualTriggers[i]] = +null_id;
    }
    d_individualTriggers.resize(d_individualTriggersSize);
  }
  
  if (d_equalityTriggers.size() > d_equalityTriggersCount) {
    // Unlink the triggers from the lists
    for (int i = d_equalityTriggers.size() - 1, i_end = d_equalityTriggersCount; i >= i_end; -- i) {
      const Trigger& trigger = d_equalityTriggers[i];
      d_nodeTriggers[trigger.classId] = trigger.nextTrigger;
    }
    // Get rid of the triggers 
    d_equalityTriggers.resize(d_equalityTriggersCount);
    d_equalityTriggersOriginal.resize(d_equalityTriggersCount);
  }

  if (d_nodes.size() > d_nodesCount) {
    // Go down the nodes, check the application nodes and remove them from use-lists
    for(int i = d_nodes.size() - 1, i_end = (int)d_nodesCount; i >= i_end; -- i) {
      // Remove from the node -> id map
      Debug("equality") << "EqualityEngine::backtrack(): removing node " << d_nodes[i] << std::endl;
      d_nodeIds.erase(d_nodes[i]);

      const FunctionApplication& app = d_applications[i];
      if (app.isApplication()) {
        // Remove from the applications map
        d_applicationLookup.erase(app);
        // Remove b from use-list
        getEqualityNode(app.b).removeTopFromUseList(d_useListNodes);
        // Remove a from use-list
        getEqualityNode(app.a).removeTopFromUseList(d_useListNodes);
      }
    }

    // Now get rid of the nodes and the rest
    d_nodes.resize(d_nodesCount);
    d_applications.resize(d_nodesCount);
    d_nodeTriggers.resize(d_nodesCount);
    d_nodeIndividualTrigger.resize(d_nodesCount);
    d_equalityGraph.resize(d_nodesCount);
    d_equalityNodes.resize(d_nodesCount);
  }
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addGraphEdge(EqualityNodeId t1, EqualityNodeId t2, MergeReasonType type, TNode reason) {
  Debug("equality") << "EqualityEngine::addGraphEdge(" << d_nodes[t1] << "," << d_nodes[t2] << "," << reason << ")" << std::endl;
  EqualityEdgeId edge = d_equalityEdges.size();
  d_equalityEdges.push_back(EqualityEdge(t2, d_equalityGraph[t1], type, reason));
  d_equalityEdges.push_back(EqualityEdge(t1, d_equalityGraph[t2], type, reason));
  d_equalityGraph[t1] = edge;
  d_equalityGraph[t2] = edge | 1;

  if (Debug.isOn("equality::internal")) {
    debugPrintGraph();
  }
}

template <typename NotifyClass>
std::string EqualityEngine<NotifyClass>::edgesToString(EqualityEdgeId edgeId) const {
  std::stringstream out;
  bool first = true;
  if (edgeId == null_edge) {
    out << "null";
  } else {
    while (edgeId != null_edge) {
      const EqualityEdge& edge = d_equalityEdges[edgeId];
      if (!first) out << ",";
      out << d_nodes[edge.getNodeId()];
      edgeId = edge.getNext();
      first = false;
    }
  }
  return out.str();
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::getExplanation(TNode t1, TNode t2, std::vector<TNode>& equalities) const {
  Debug("equality") << "EqualityEngine::getExplanation(" << t1 << "," << t2 << ")" << std::endl;

  Assert(getRepresentative(t1) == getRepresentative(t2));

  // Get the explanation
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);
  getExplanation(t1Id, t2Id, equalities);
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::getExplanation(EqualityNodeId t1Id, EqualityNodeId t2Id, std::vector<TNode>& equalities) const {

  Debug("equality") << "EqualityEngine::getExplanation(" << d_nodes[t1Id] << "," << d_nodes[t2Id] << ")" << std::endl;

  // If the nodes are the same, we're done
  if (t1Id == t2Id) return;

  if (Debug.isOn("equality::internal")) {
    debugPrintGraph();
  }

  // Queue for the BFS containing nodes
  std::vector<BfsData> bfsQueue;

  // Find a path from t1 to t2 in the graph (BFS)
  bfsQueue.push_back(BfsData(t1Id, null_id, 0));
  size_t currentIndex = 0;
  while (true) {
    // There should always be a path, and every node can be visited only once (tree)
    Assert(currentIndex < bfsQueue.size());

    // The next node to visit
    BfsData current = bfsQueue[currentIndex];
    EqualityNodeId currentNode = current.nodeId;

    Debug("equality") << "EqualityEngine::getExplanation(): currentNode =  " << d_nodes[currentNode] << std::endl;

    // Go through the equality edges of this node
    EqualityEdgeId currentEdge = d_equalityGraph[currentNode];
    Debug("equality") << "EqualityEngine::getExplanation(): edgesId =  " << currentEdge << std::endl;
    Debug("equality") << "EqualityEngine::getExplanation(): edges =  " << edgesToString(currentEdge) << std::endl;

    while (currentEdge != null_edge) {
      // Get the edge
      const EqualityEdge& edge = d_equalityEdges[currentEdge];

      // If not just the backwards edge
      if ((currentEdge | 1u) != (current.edgeId | 1u)) {

        Debug("equality") << "EqualityEngine::getExplanation(): currentEdge = (" << d_nodes[currentNode] << "," << d_nodes[edge.getNodeId()] << ")" << std::endl;

        // Did we find the path
        if (edge.getNodeId() == t2Id) {

          Debug("equality") << "EqualityEngine::getExplanation(): path found: " << std::endl;

          // Reconstruct the path
          do {
            // The current node
            currentNode = bfsQueue[currentIndex].nodeId;
            EqualityNodeId edgeNode = d_equalityEdges[currentEdge].getNodeId();
            MergeReasonType reasonType = d_equalityEdges[currentEdge].getReasonType();

            Debug("equality") << "EqualityEngine::getExplanation(): currentEdge = " << currentEdge << ", currentNode = " << currentNode << std::endl;

            // Add the actual equality to the vector
            if (reasonType == MERGED_THROUGH_CONGRUENCE) {
              // f(x1, x2) == f(y1, y2) because x1 = y1 and x2 = y2
              Debug("equality") << "EqualityEngine::getExplanation(): due to congruence, going deeper" << std::endl;
              const FunctionApplication& f1 = d_applications[currentNode];
              const FunctionApplication& f2 = d_applications[edgeNode];
              Debug("equality") << push;
              getExplanation(f1.a, f2.a, equalities);
              getExplanation(f1.b, f2.b, equalities);
              Debug("equality") << pop;
            } else {
              // Construct the equality
              Debug("equality") << "EqualityEngine::getExplanation(): adding: " << d_equalityEdges[currentEdge].getReason() << std::endl;
              equalities.push_back(d_equalityEdges[currentEdge].getReason());
            }

            // Go to the previous
            currentEdge = bfsQueue[currentIndex].edgeId;
            currentIndex = bfsQueue[currentIndex].previousIndex;
          } while (currentEdge != null_id);

          // Done
          return;
        }

        // Push to the visitation queue if it's not the backward edge
        bfsQueue.push_back(BfsData(edge.getNodeId(), currentEdge, currentIndex));
      }

      // Go to the next edge
      currentEdge = edge.getNext();
    }

    // Go to the next node to visit
    ++ currentIndex;
  }
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addTriggerDisequality(TNode t1, TNode t2, TNode trigger) {
  Node equality = t1.eqNode(t2);
  addTerm(equality);
  addTriggerEquality(equality, d_false, trigger);
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addTriggerEquality(TNode t1, TNode t2, TNode trigger) {

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << ", " << t2 << ", " << trigger << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Get the information about t1
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t1classId = getEqualityNode(t1Id).getFind();
  TriggerId t1TriggerId = d_nodeTriggers[t1Id];

  // Get the information about t2
  EqualityNodeId t2Id = getNodeId(t2);
  EqualityNodeId t2classId = getEqualityNode(t2Id).getFind();
  TriggerId t2TriggerId = d_nodeTriggers[t2Id];

  Debug("equality") << "EqualityEngine::addTrigger(" << trigger << "): " << t1Id << " (" << t1classId << ") = " << t2Id << " (" << t2classId << ")" << std::endl;

  // Create the triggers
  TriggerId t1NewTriggerId = d_equalityTriggers.size();
  TriggerId t2NewTriggerId = t1NewTriggerId | 1;
  d_equalityTriggers.push_back(Trigger(t1classId, t1TriggerId));
  d_equalityTriggersOriginal.push_back(trigger);
  d_equalityTriggers.push_back(Trigger(t2classId, t2TriggerId));
  d_equalityTriggersOriginal.push_back(trigger);

  // Update the counters
  d_equalityTriggersCount = d_equalityTriggersCount + 2;

  // Add the trigger to the trigger graph
  d_nodeTriggers[t1classId] = t1NewTriggerId;
  d_nodeTriggers[t2classId] = t2NewTriggerId;

  // If the trigger is already on, we propagate
  if (t1classId == t2classId) {
    Debug("equality") << "EqualityEngine::addTrigger(" << t1 << "," << t2 << "): triggered at setup time" << std::endl;
    if (d_performNotify) {
      d_notify.notify(trigger); // Don't care about the return value
    }
  }

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << "," << t2 << ") => (" << t1NewTriggerId << ", " << t2NewTriggerId << ")" << std::endl;
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::propagate() {

  Debug("equality") << "EqualityEngine::propagate()" << std::endl;

  bool done = false;
  while (!d_propagationQueue.empty()) {

    // The current merge candidate
    const MergeCandidate current = d_propagationQueue.front();
    d_propagationQueue.pop();

    if (done) {
      // If we're done, just empty the queue
      continue;
    }

    // Get the representatives
    EqualityNodeId t1classId = getEqualityNode(current.t1Id).getFind();
    EqualityNodeId t2classId = getEqualityNode(current.t2Id).getFind();

    // If already the same, we're done
    if (t1classId == t2classId) {
      continue;
    }

    // Get the nodes of the representatives
    EqualityNode& node1 = getEqualityNode(t1classId);
    EqualityNode& node2 = getEqualityNode(t2classId);

    Assert(node1.getFind() == t1classId);
    Assert(node2.getFind() == t2classId);

    // Add the actuall equality to the equality graph
    addGraphEdge(current.t1Id, current.t2Id, current.type, current.reason);

    // One more equality added
    d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;

    // Depending on the merge preference (such as size), merge them
    std::vector<TriggerId> triggers;
    if (node2.getSize() > node1.getSize()) {
      Debug("equality") << "EqualityEngine::propagate(): merging " << d_nodes[current.t1Id]<< " into " << d_nodes[current.t2Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t2classId, t1classId));
      merge(node2, node1, triggers);
    } else {
      Debug("equality") << "EqualityEngine::propagate(): merging " << d_nodes[current.t2Id] << " into " << d_nodes[current.t1Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t1classId, t2classId));
      merge(node1, node2, triggers);
    }

    // Notify the triggers
    if (d_performNotify) {
      for (size_t trigger = 0, trigger_end = triggers.size(); trigger < trigger_end && !done; ++ trigger) {
        // Notify the trigger and exit if it fails
        done = !d_notify.notify(d_equalityTriggersOriginal[triggers[trigger]]);
      }
    }
  }
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::debugPrintGraph() const {
  for (EqualityNodeId nodeId = 0; nodeId < d_nodes.size(); ++ nodeId) {

    Debug("equality::internal") << d_nodes[nodeId] << " " << nodeId << "(" << getEqualityNode(nodeId).getFind() << "):";

    EqualityEdgeId edgeId = d_equalityGraph[nodeId];
    while (edgeId != null_edge) {
      const EqualityEdge& edge = d_equalityEdges[edgeId];
      Debug("equality::internal") << " " << d_nodes[edge.getNodeId()] << ":" << edge.getReason();
      edgeId = edge.getNext();
    }

    Debug("equality::internal") << std::endl;
  }
}

class ScopedBool {
  bool& watch;
  bool oldValue;
public:
  ScopedBool(bool& watch, bool newValue)
  : watch(watch), oldValue(watch) {
    watch = newValue;
  }
  ~ScopedBool() {
    watch = oldValue;
  }
};

template <typename NotifyClass>
bool EqualityEngine<NotifyClass>::areEqual(TNode t1, TNode t2)
{
  // Don't notify during this check
  ScopedBool turnOfNotify(d_performNotify, false);

  // Push the context, so that we can remove the terms later
  d_context->push();

  // Add the terms
  addTerm(t1);
  addTerm(t2);
  bool equal = getEqualityNode(t1).getFind() == getEqualityNode(t2).getFind();

  // Pop the context (triggers new term removal)
  d_context->pop();

  // Return whether the two terms are equal
  return equal;
}

template <typename NotifyClass>
bool EqualityEngine<NotifyClass>::areDisequal(TNode t1, TNode t2)
{
  // Don't notify during this check
  ScopedBool turnOfNotify(d_performNotify, false);

  // Push the context, so that we can remove the terms later
  d_context->push();

  // Add the terms
  addTerm(t1);
  addTerm(t2);

  // Check (t1 = t2) = false
  Node equality1 = t1.eqNode(t2);
  addTerm(equality1);
  if (getEqualityNode(equality1).getFind() == getEqualityNode(d_false).getFind()) {
    return true;
  }

  // Check (t2 = t1) = false
  Node equality2 = t2.eqNode(t1);
  addTerm(equality2);
  if (getEqualityNode(equality2).getFind() == getEqualityNode(d_false).getFind()) {
    return true;
  }

  // Pop the context (triggers new term removal)
  d_context->pop();

  // Return whether the terms are disequal
  return false;
}

template <typename NotifyClass>
void EqualityEngine<NotifyClass>::addTriggerTerm(TNode t) 
{
  Debug("equality::internal") << "EqualityEngine::addTriggerTerm(" << t << ")" << std::endl;

  // Add the term if it's not already there
  addTerm(t);

  // Get the node id
  EqualityNodeId eqNodeId = getNodeId(t);
  EqualityNode& eqNode = getEqualityNode(eqNodeId);
  EqualityNodeId classId = eqNode.getFind();

  if (d_nodeIndividualTrigger[classId] != +null_id) {  
    // No need to keep it, just propagate the existing individual triggers
    if (d_performNotify) {
      d_notify.notify(t, d_nodes[d_nodeIndividualTrigger[classId]]); 
    }
  } else {
    // Add it to the list for backtracking
    d_individualTriggers.push_back(classId);
    d_individualTriggersSize = d_individualTriggersSize + 1; 
    // Mark the class id as a trigger
    d_nodeIndividualTrigger[classId] = eqNodeId;
  }
}

template <typename NotifyClass>
bool  EqualityEngine<NotifyClass>::isTriggerTerm(TNode t) const {
  if (!hasTerm(t)) return false;
  EqualityNodeId classId = getEqualityNode(t).getFind();
  return d_nodeIndividualTrigger[classId] != +null_id;
}

} // Namespace uf
} // Namespace theory
} // Namespace CVC4

