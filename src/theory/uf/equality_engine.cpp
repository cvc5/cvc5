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

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace eq {

/**
 * Data used in the BFS search through the equality graph.
 */
struct BfsData {
  // The current node
  EqualityNodeId nodeId;
  // The index of the edge we traversed
  EqualityEdgeId edgeId;
  // Index in the queue of the previous node. Shouldn't be too much of them, at most the size
  // of the biggest equivalence class
  size_t previousIndex;

  BfsData(EqualityNodeId nodeId = null_id, EqualityEdgeId edgeId = null_edge, size_t prev = 0)
  : nodeId(nodeId), edgeId(edgeId), previousIndex(prev) {}
};

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

EqualityEngineNotifyNone EqualityEngine::s_notifyNone;

void EqualityEngine::init() {
  Debug("equality") << "EqualityEdge::EqualityEngine(): id_null = " << +null_id << std::endl;
  Debug("equality") << "EqualityEdge::EqualityEngine(): edge_null = " << +null_edge << std::endl;
  Debug("equality") << "EqualityEdge::EqualityEngine(): trigger_null = " << +null_trigger << std::endl;

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  addTerm(d_true);
  addTerm(d_false);

  d_trueId = getNodeId(d_true);
  d_falseId = getNodeId(d_false);  

  d_triggerDatabaseAllocatedSize = 100000;
  d_triggerDatabase = (char*) malloc(d_triggerDatabaseAllocatedSize);
} 

EqualityEngine::~EqualityEngine() throw(AssertionException) {
  free(d_triggerDatabase);
}


EqualityEngine::EqualityEngine(context::Context* context, std::string name) 
: ContextNotifyObj(context)
, d_context(context)
, d_done(context, false)
, d_performNotify(true)
, d_notify(s_notifyNone)
, d_applicationLookupsCount(context, 0)
, d_nodesCount(context, 0)
, d_assertedEqualitiesCount(context, 0)
, d_equalityTriggersCount(context, 0)
, d_stats(name)
, d_triggerDatabaseSize(context, 0)
, d_triggerTermSetUpdatesSize(context, 0)
, d_deducedDisequalitiesSize(context, 0)
{
  init();
}

EqualityEngine::EqualityEngine(EqualityEngineNotify& notify, context::Context* context, std::string name)
: ContextNotifyObj(context)
, d_context(context)
, d_done(context, false)
, d_performNotify(true)
, d_notify(notify)
, d_applicationLookupsCount(context, 0)
, d_nodesCount(context, 0)
, d_assertedEqualitiesCount(context, 0)
, d_equalityTriggersCount(context, 0)
, d_stats(name)
, d_triggerDatabaseSize(context, 0)
, d_triggerTermSetUpdatesSize(context, 0)
, d_deducedDisequalitiesSize(context, 0)
{
  init();
}

void EqualityEngine::enqueue(const MergeCandidate& candidate) {
    d_propagationQueue.push(candidate);
}

EqualityNodeId EqualityEngine::newApplicationNode(TNode original, EqualityNodeId t1, EqualityNodeId t2, bool isEquality) {
  Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ")" << std::endl;

  ++ d_stats.functionTermsCount;

  // Get another id for this
  EqualityNodeId funId = newNode(original);
  FunctionApplication funOriginal(isEquality, t1, t2);
  // The function application we're creating
  EqualityNodeId t1ClassId = getEqualityNode(t1).getFind();
  EqualityNodeId t2ClassId = getEqualityNode(t2).getFind();
  FunctionApplication funNormalized(isEquality, t1ClassId, t2ClassId);

  // We add the original version
  d_applications[funId] = FunctionApplicationPair(funOriginal, funNormalized);

  // Add the lookup data, if it's not already there
  ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
  if (find == d_applicationLookup.end()) {
    // When we backtrack, if the lookup is not there anymore, we'll add it again
    Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): no lookup, setting up" << std::endl;
    // Mark the normalization to the lookup
    storeApplicationLookup(funNormalized, funId);
    // If an equality, we do some extra reasoning 
    if (isEquality && d_isConstant[t1ClassId] && d_isConstant[t2ClassId]) {
      if (t1ClassId != t2ClassId) {
        Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): got constants" << std::endl;
        enqueue(MergeCandidate(funId, d_falseId, MERGED_THROUGH_CONSTANTS, TNode::null()));
      }
    }
  } else {
    // If it's there, we need to merge these two
    Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): lookup exists, adding to queue" << std::endl;
    enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
  }

  // Add to the use lists
  d_equalityNodes[t1ClassId].usedIn<USE_LIST_FUNCTIONS>(funId, d_useListNodes);
  d_equalityNodes[t2ClassId].usedIn<USE_LIST_FUNCTIONS>(funId, d_useListNodes);

  // Return the new id
  Debug("equality") << "EqualityEngine::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ") => " << funId << std::endl;

  return funId;
}

EqualityNodeId EqualityEngine::newNode(TNode node) {

  Debug("equality") << "EqualityEngine::newNode(" << node << ")" << std::endl;

  ++ d_stats.termsCount;

  // Register the new id of the term
  EqualityNodeId newId = d_nodes.size();
  d_nodeIds[node] = newId;
  // Add the node to it's position
  d_nodes.push_back(node);
  // Note if this is an application or not
  d_applications.push_back(FunctionApplicationPair());
  // Add the trigger list for this node
  d_nodeTriggers.push_back(+null_trigger);
  // Add it to the equality graph
  d_equalityGraph.push_back(+null_edge);
  // Mark the no-individual trigger
  d_nodeIndividualTrigger.push_back(+null_set_id);
  // Mark non-constant by default
  d_isConstant.push_back(node.isConst());
  // Mark Boolean nodes
  d_isBoolean.push_back(false);
  // Add the equality node to the nodes
  d_equalityNodes.push_back(EqualityNode(newId));

  // Increase the counters
  d_nodesCount = d_nodesCount + 1;

  Debug("equality") << "EqualityEngine::newNode(" << node << ") => " << newId << std::endl;

  return newId;
}

void EqualityEngine::addTerm(TNode t) {

  Debug("equality") << "EqualityEngine::addTerm(" << t << ")" << std::endl;

  // If there already, we're done
  if (hasTerm(t)) {
    Debug("equality") << "EqualityEngine::addTerm(" << t << "): already there" << std::endl;
    return;
  }

  if (d_done) {
    return;
  }

  EqualityNodeId result;

  if (t.getKind() == kind::EQUAL) {
    addTerm(t[0]);
    addTerm(t[1]);
    result = newApplicationNode(t, getNodeId(t[0]), getNodeId(t[1]), true); 
  } else if (t.getNumChildren() > 0 && d_congruenceKinds[t.getKind()]) {
    // Add the operator
    TNode tOp = t.getOperator();
    addTerm(tOp);
    // Add all the children and Curryfy
    result = getNodeId(tOp);
    for (unsigned i = 0; i < t.getNumChildren(); ++ i) {
      // Add the child
      addTerm(t[i]);
      // Add the application
      result = newApplicationNode(t, result, getNodeId(t[i]), false);
    }
  } else {
    // Otherwise we just create the new id
    result = newNode(t);
  }

  if (t.getType().isBoolean()) {
    // We set this here as this only applies to actual terms, not the
    // intermediate application terms
    d_isBoolean[result] = true;
  }

  propagate();

  Debug("equality") << "EqualityEngine::addTerm(" << t << ") => " << result << std::endl;
}

bool EqualityEngine::hasTerm(TNode t) const {
  return d_nodeIds.find(t) != d_nodeIds.end();
}

EqualityNodeId EqualityEngine::getNodeId(TNode node) const {
  Assert(hasTerm(node), node.toString().c_str());
  return (*d_nodeIds.find(node)).second;
}

EqualityNode& EqualityEngine::getEqualityNode(TNode t) {
  return getEqualityNode(getNodeId(t));
}

EqualityNode& EqualityEngine::getEqualityNode(EqualityNodeId nodeId) {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

const EqualityNode& EqualityEngine::getEqualityNode(TNode t) const {
  return getEqualityNode(getNodeId(t));
}

const EqualityNode& EqualityEngine::getEqualityNode(EqualityNodeId nodeId) const {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

void EqualityEngine::assertEqualityInternal(TNode t1, TNode t2, TNode reason) {

  Debug("equality") << "EqualityEngine::addEqualityInternal(" << t1 << "," << t2 << ")" << std::endl;

  if (d_done) {
    return;
  }

  // Add the terms if they are not already in the database
  addTerm(t1);
  addTerm(t2);

  // Add to the queue and propagate
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);
  enqueue(MergeCandidate(t1Id, t2Id, MERGED_THROUGH_EQUALITY, reason));
}

void EqualityEngine::assertPredicate(TNode t, bool polarity, TNode reason) {
  Debug("equality") << "EqualityEngine::addPredicate(" << t << "," << (polarity ? "true" : "false") << ")" << std::endl;
  Assert(t.getKind() != kind::EQUAL, "Use assertEquality instead");
  assertEqualityInternal(t, polarity ? d_true : d_false, reason);
  propagate();
}

void EqualityEngine::assertEquality(TNode eq, bool polarity, TNode reason) {
  Debug("equality") << "EqualityEngine::addEquality(" << eq << "," << (polarity ? "true" : "false") << std::endl;
  if (polarity) {
    // If two terms are already equal, don't assert anything
    if (hasTerm(eq[0]) && hasTerm(eq[1]) && areEqual(eq[0], eq[1])) {
      return;
    }
    // Add equality between terms
    assertEqualityInternal(eq[0], eq[1], reason);
    propagate();
    // Add eq = true for dis-equality propagation
    assertEqualityInternal(eq, d_true, reason);
    propagate();    
  } else {
    // If two terms are already dis-equal, don't assert anything
    if (hasTerm(eq[0]) && hasTerm(eq[1]) && areDisequal(eq[0], eq[1], false)) {
      return;
    }
    
    assertEqualityInternal(eq, d_false, reason);
    propagate();    
    assertEqualityInternal(eq[1].eqNode(eq[0]), d_false, reason);
    propagate();
  
    if (d_done) {
      return;
    }
  
    // If we are adding a disequality, notify of the shared term representatives
    EqualityNodeId a = getNodeId(eq[0]);
    EqualityNodeId b = getNodeId(eq[1]);
    EqualityNodeId eqId = getNodeId(eq);
    TriggerTermSetRef aTriggerRef = d_nodeIndividualTrigger[a];
    TriggerTermSetRef bTriggerRef = d_nodeIndividualTrigger[b];
    if (aTriggerRef != +null_set_id && bTriggerRef != +null_set_id) {
      // The sets of trigger terms
      TriggerTermSet& aTriggerTerms = getTriggerTermSet(aTriggerRef);
      TriggerTermSet& bTriggerTerms = getTriggerTermSet(bTriggerRef);
      // Go through and notify the shared dis-equalities 
      Theory::Set aTags = aTriggerTerms.tags;           
      Theory::Set bTags = bTriggerTerms.tags;           
      TheoryId aTag = Theory::setPop(aTags);
      TheoryId bTag = Theory::setPop(bTags);
      int a_i = 0, b_i = 0;
      while (aTag != THEORY_LAST && bTag != THEORY_LAST) {
        if (aTag < bTag) {
          aTag = Theory::setPop(aTags);
          ++ a_i;                  
        } else if (aTag > bTag) {
          bTag = Theory::setPop(bTags);
          ++ b_i;
        } else {
          // Same tags, notify
          EqualityNodeId aSharedId = aTriggerTerms.triggers[a_i++];
          EqualityNodeId bSharedId = bTriggerTerms.triggers[b_i++];
          d_deducedDisequalityReasons.push_back(EqualityPair(aSharedId, a));
          d_deducedDisequalityReasons.push_back(EqualityPair(bSharedId, b));
          d_deducedDisequalityReasons.push_back(EqualityPair(eqId, d_falseId));
          storePropagatedDisequality(d_nodes[aSharedId], d_nodes[bSharedId], 3);
          // We notify even if the it's already been sent (they are not 
          // disequal at assertion, and we need to notify for each tag) 
          if (!d_notify.eqNotifyTriggerTermEquality(aTag, d_nodes[aSharedId], d_nodes[bSharedId], false)) {
            break;
          }
          // Pop the next tags
          aTag = Theory::setPop(aTags);
          bTag = Theory::setPop(bTags);
        }
      }
    }
  }
}

TNode EqualityEngine::getRepresentative(TNode t) const {
  Debug("equality::internal") << "EqualityEngine::getRepresentative(" << t << ")" << std::endl;
  Assert(hasTerm(t));
  EqualityNodeId representativeId = getEqualityNode(t).getFind();
  Debug("equality::internal") << "EqualityEngine::getRepresentative(" << t << ") => " << d_nodes[representativeId] << std::endl;
  return d_nodes[representativeId];
}

bool EqualityEngine::merge(EqualityNode& class1, EqualityNode& class2, std::vector<TriggerId>& triggersFired) {

  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << ")" << std::endl;

  Assert(triggersFired.empty());

  ++ d_stats.mergesCount;

  EqualityNodeId class1Id = class1.getFind();
  EqualityNodeId class2Id = class2.getFind();

  // Check for constant merges
  bool isConstant = d_isConstant[class1Id];

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
          const TriggerInfo& triggerInfo = d_equalityTriggersOriginal[currentTrigger];
          if (triggerInfo.trigger.getKind() == kind::EQUAL && !triggerInfo.polarity) {
            TNode equality = triggerInfo.trigger;
            EqualityNodeId original = getNodeId(equality);
            d_deducedDisequalityReasons.push_back(EqualityPair(original, d_falseId));
            if (!storePropagatedDisequality(equality[0], equality[1], 1)) {
              // Go to the next trigger
              currentTrigger = trigger.nextTrigger;
              continue;
            }
          }
          // Id of the real trigger is half the internal one
          triggersFired.push_back(currentTrigger);
        }
      }

      // Go to the next trigger
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Update class2 table lookup and information if not a boolean
  // since booleans can't be in an application
  if (!d_isBoolean[class2Id]) {
    Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of " << class2Id << std::endl;
    do {
      // Get the current node
      EqualityNode& currentNode = getEqualityNode(currentId);    
      Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of node " << currentId << std::endl;
 
      // Go through the uselist and check for congruences
      UseListNodeId currentUseId = currentNode.getUseList<USE_LIST_FUNCTIONS>();
      while (currentUseId != null_uselist_id) {
        // Get the node of the use list
        UseListNode& useNode = d_useListNodes[currentUseId];
        // Get the function application
        EqualityNodeId funId = useNode.getApplicationId();
        Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << "): " << currentId << " in " << d_nodes[funId] << std::endl;
        const FunctionApplication& fun = d_applications[useNode.getApplicationId()].normalized;
        // Check if there is an application with find arguments
        EqualityNodeId aNormalized = getEqualityNode(fun.a).getFind();
        EqualityNodeId bNormalized = getEqualityNode(fun.b).getFind();
        FunctionApplication funNormalized(fun.isEquality, aNormalized, bNormalized);
        ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
        if (find != d_applicationLookup.end()) {
          // Applications fun and the funNormalized can be merged due to congruence
          if (getEqualityNode(funId).getFind() != getEqualityNode(find->second).getFind()) {
            enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
          }
        } else {
          // There is no representative, so we can add one, we remove this when backtracking
          storeApplicationLookup(funNormalized, funId);
          // Now, if we're constant and it's an equality, check if the other guy is also a constant
          if (isConstant && funNormalized.isEquality) {
            if (d_isConstant[funNormalized.a] && d_isConstant[funNormalized.b]) {
              // both constants
              if (funNormalized.a != funNormalized.b) {
                enqueue(MergeCandidate(funId, d_falseId, MERGED_THROUGH_CONSTANTS, TNode::null()));
              }
            }
          }          
        }
   
        // Go to the next one in the use list
        currentUseId = useNode.getNext();
      }
  
      // Move to the next node
      currentId = currentNode.getNext();
    } while (currentId != class2Id);
  }
    
  // Now merge the lists
  class1.merge<true>(class2);
  
  // Notify the trigger term merges
  TriggerTermSetRef class2triggerRef = d_nodeIndividualTrigger[class2Id];
  if (class2triggerRef != +null_set_id) {
    TriggerTermSetRef class1triggerRef = d_nodeIndividualTrigger[class1Id];
    if (class1triggerRef == +null_set_id) {
      // If class1 doesn't have individual triggers, but class2 does, mark it
      d_nodeIndividualTrigger[class1Id] = class2triggerRef;
      // Add it to the list for backtracking
      d_triggerTermSetUpdates.push_back(TriggerSetUpdate(class1Id, +null_set_id));
      d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
    } else {
      // Get the triggers
      TriggerTermSet& class1triggers = getTriggerTermSet(class1triggerRef);
      TriggerTermSet& class2triggers = getTriggerTermSet(class2triggerRef);
      
      // Initialize the merged set
      d_newSetTags = Theory::setUnion(class1triggers.tags, class2triggers.tags);
      d_newSetTriggersSize = 0;
      
      int i1 = 0;
      int i2 = 0;
      Theory::Set tags1 = class1triggers.tags;
      Theory::Set tags2 = class2triggers.tags;
      TheoryId tag1 = Theory::setPop(tags1);
      TheoryId tag2 = Theory::setPop(tags2);
      
      // Comparing the THEORY_LAST is OK because all other theories are
      // smaller, and will therefore be preferred
      while (tag1 != THEORY_LAST || tag2 != THEORY_LAST) 
      {
        if (tag1 < tag2) {
          // copy tag1 
          d_newSetTriggers[d_newSetTriggersSize++] = class1triggers.triggers[i1++];
          tag1 = Theory::setPop(tags1);
        } else if (tag1 > tag2) {
          // copy tag2
          d_newSetTriggers[d_newSetTriggersSize++] = class2triggers.triggers[i2++];
          tag2 = Theory::setPop(tags2);
        } else {
          // copy tag1 
          EqualityNodeId tag1id = d_newSetTriggers[d_newSetTriggersSize++] = class1triggers.triggers[i1++];
          // since they are both tagged notify of merge
          if (d_performNotify) {
            EqualityNodeId tag2id = class2triggers.triggers[i2++];
            if (!d_notify.eqNotifyTriggerTermEquality(tag1, d_nodes[tag1id], d_nodes[tag2id], true)) {
              return false;
            }
          }
          // Next tags
          tag1 = Theory::setPop(tags1);
          tag2 = Theory::setPop(tags2);
        }
      }   
      
      // Add the new trigger set, if different from previous one
      if (class1triggers.tags != class2triggers.tags) {
        // Add it to the list for backtracking
        d_triggerTermSetUpdates.push_back(TriggerSetUpdate(class1Id, class1triggerRef));
        d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
        // Mark the the new set as a trigger 
        d_nodeIndividualTrigger[class1Id] = newTriggerTermSet();
      }  
    }	
  }

  // Notify of the constants merge
  if (isConstant && d_isConstant[class2Id]) {
    if (d_performNotify) {
      if (!d_notify.eqNotifyConstantTermMerge(d_nodes[class1Id], d_nodes[class2Id])) {
        return false;
      }
    }
  }

  // Everything fine
  return true;
}

void EqualityEngine::undoMerge(EqualityNode& class1, EqualityNode& class2, EqualityNodeId class2Id) {

  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << ")" << std::endl;

  // Now unmerge the lists (same as merge)
  class1.merge<false>(class2);

  // Update class2 representative information
  EqualityNodeId currentId = class2Id;
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

}

void EqualityEngine::backtrack() {

  Debug("equality::backtrack") << "backtracking" << std::endl;

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

  if (d_triggerTermSetUpdates.size() > d_triggerTermSetUpdatesSize) {
    // Unset the individual triggers
    for (int i = d_triggerTermSetUpdates.size() - 1, i_end = d_triggerTermSetUpdatesSize; i >= i_end; -- i) {
      const TriggerSetUpdate& update = d_triggerTermSetUpdates[i];
      d_nodeIndividualTrigger[update.classId] = update.oldValue;
    }
    d_triggerTermSetUpdates.resize(d_triggerTermSetUpdatesSize);
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

  if (d_applicationLookups.size() > d_applicationLookupsCount) {
    for (int i = d_applicationLookups.size() - 1, i_end = (int) d_applicationLookupsCount; i >= i_end; -- i) {
      d_applicationLookup.erase(d_applicationLookups[i]);
    }
    d_applicationLookups.resize(d_applicationLookupsCount);
  }

  if (d_nodes.size() > d_nodesCount) {
    // Go down the nodes, check the application nodes and remove them from use-lists
    for(int i = d_nodes.size() - 1, i_end = (int)d_nodesCount; i >= i_end; -- i) {
      // Remove from the node -> id map
      Debug("equality") << "EqualityEngine::backtrack(): removing node " << d_nodes[i] << std::endl;
      d_nodeIds.erase(d_nodes[i]);

      const FunctionApplication& app = d_applications[i].normalized;
      if (app.isApplication()) {
        // Remove b from use-list
        getEqualityNode(app.b).removeTopFromUseList<USE_LIST_FUNCTIONS>(d_useListNodes);
        // Remove a from use-list
        getEqualityNode(app.a).removeTopFromUseList<USE_LIST_FUNCTIONS>(d_useListNodes);
      }
    }

    // Now get rid of the nodes and the rest
    d_nodes.resize(d_nodesCount);
    d_applications.resize(d_nodesCount);
    d_nodeTriggers.resize(d_nodesCount);
    d_nodeIndividualTrigger.resize(d_nodesCount);
    d_isConstant.resize(d_nodesCount);
    d_isBoolean.resize(d_nodesCount);
    d_equalityGraph.resize(d_nodesCount);
    d_equalityNodes.resize(d_nodesCount);
  }

  if (d_deducedDisequalities.size() > d_deducedDisequalitiesSize) {
    for(int i = d_deducedDisequalities.size() - 1, i_end = (int)d_deducedDisequalitiesSize; i >= i_end; -- i) {
      EqualityPair pair = d_deducedDisequalities[i];
      DisequalityReasonRef reason = d_disequalityReasonsMap[pair];
      // Remove from the map
      d_disequalityReasonsMap.erase(pair);
      std::swap(pair.first, pair.second);
      d_disequalityReasonsMap.erase(pair);
      // Resize the reasons vector
      d_deducedDisequalityReasons.resize(reason.mergesStart);
    }
    d_deducedDisequalities.resize(d_deducedDisequalitiesSize);
  }
}

void EqualityEngine::addGraphEdge(EqualityNodeId t1, EqualityNodeId t2, MergeReasonType type, TNode reason) {
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

std::string EqualityEngine::edgesToString(EqualityEdgeId edgeId) const {
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

void EqualityEngine::explainEquality(TNode t1, TNode t2, bool polarity, std::vector<TNode>& equalities) const {
  Debug("equality") << "EqualityEngine::explainEquality(" << t1 << ", " << t2 << ", " << (polarity ? "true" : "false") << ")" << std::endl;

  // The terms must be there already
  Assert(hasTerm(t1) && hasTerm(t2));;

  // Get the ids
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);

  if (polarity) {
    // Get the explanation
    getExplanation(t1Id, t2Id, equalities);
  } else {
    // Get the reason for this disequality
    EqualityPair pair(t1Id, t2Id);
    Assert(d_disequalityReasonsMap.find(pair) != d_disequalityReasonsMap.end(), "Don't ask for stuff I didn't notify you about");
    DisequalityReasonRef reasonRef = d_disequalityReasonsMap.find(pair)->second;
    for (unsigned i = reasonRef.mergesStart; i < reasonRef.mergesEnd; ++ i) {
      EqualityPair toExplain = d_deducedDisequalityReasons[i];
      getExplanation(toExplain.first, toExplain.second, equalities);
    }
  }
}

void EqualityEngine::explainPredicate(TNode p, bool polarity, std::vector<TNode>& assertions) const {
  Debug("equality") << "EqualityEngine::explainPredicate(" << p << ")" << std::endl;
  // Must have the term
  Assert(hasTerm(p));
  // Get the explanation
  getExplanation(getNodeId(p), polarity ? d_trueId : d_falseId, assertions);
}

void EqualityEngine::getExplanation(EqualityNodeId t1Id, EqualityNodeId t2Id, std::vector<TNode>& equalities) const {

  Debug("equality") << "EqualityEngine::getExplanation(" << d_nodes[t1Id] << "," << d_nodes[t2Id] << ")" << std::endl;

  // We can only explain the nodes that got merged
#ifdef CVC4_ASSERTIONS
  bool canExplain = getEqualityNode(t1Id).getFind() == getEqualityNode(t2Id).getFind();
  if (!canExplain) {
    Warning() << "Can't explain equality:" << std::endl;
    Warning() << d_nodes[t1Id] << " with find " << d_nodes[getEqualityNode(t1Id).getFind()] << std::endl;
    Warning() << d_nodes[t2Id] << " with find " << d_nodes[getEqualityNode(t2Id).getFind()] << std::endl;    
  }
  Assert(canExplain);
#endif

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
            switch (reasonType) {
            case MERGED_THROUGH_CONGRUENCE: {
              // f(x1, x2) == f(y1, y2) because x1 = y1 and x2 = y2
              Debug("equality") << "EqualityEngine::getExplanation(): due to congruence, going deeper" << std::endl;
              const FunctionApplication& f1 = d_applications[currentNode].original;
              const FunctionApplication& f2 = d_applications[edgeNode].original;
              Debug("equality") << push;
              getExplanation(f1.a, f2.a, equalities);
              getExplanation(f1.b, f2.b, equalities);
              Debug("equality") << pop;
              break;
            } 
            case MERGED_THROUGH_EQUALITY:
              // Construct the equality
              Debug("equality") << "EqualityEngine::getExplanation(): adding: " << d_equalityEdges[currentEdge].getReason() << std::endl;
              equalities.push_back(d_equalityEdges[currentEdge].getReason());
              break;
            case MERGED_THROUGH_CONSTANTS: {
              // (a = b) == false because a and b are different constants
              Debug("equality") << "EqualityEngine::getExplanation(): due to constants, going deeper" << std::endl;
              EqualityNodeId eqId = currentNode == d_falseId ? edgeNode : currentNode;
              const FunctionApplication& eq = d_applications[eqId].original;
              Assert(eq.isEquality, "Must be an equality");
              
              Debug("equality") << push;
              // Explain why a is a constant
              getExplanation(eq.a, getEqualityNode(eq.a).getFind(), equalities);
              // Explain why b is a constant
              getExplanation(eq.b, getEqualityNode(eq.b).getFind(), equalities);
              Debug("equality") << pop;
            
              break;
            }
            default:
              Unreachable();
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

void EqualityEngine::addTriggerEquality(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL);

  if (d_done) {
    return;
  }

  // Add the terms
  addTerm(eq[0]);
  addTerm(eq[1]);

  bool skipTrigger = false;

  // If they are equal or disequal already, no need for the trigger
  if (areEqual(eq[0], eq[1])) {
    d_notify.eqNotifyTriggerEquality(eq, true);
    skipTrigger = true;
  }
  if (areDisequal(eq[0], eq[1], true)) {
    d_notify.eqNotifyTriggerEquality(eq, false);
    skipTrigger = true;
  }

  if (skipTrigger) {
    return;
  }

  // Add the equality
  addTerm(eq);

  // Positive trigger
  addTriggerEqualityInternal(eq[0], eq[1], eq, true);
  // Negative trigger
  addTriggerEqualityInternal(eq, d_false, eq, false);
}

void EqualityEngine::addTriggerPredicate(TNode predicate) {
  Assert(predicate.getKind() != kind::NOT && predicate.getKind() != kind::EQUAL);
  Assert(d_congruenceKinds.tst(predicate.getKind()), "No point in adding non-congruence predicates");

  if (d_done) {
    return;
  }

  // Add the term
  addTerm(predicate);

  bool skipTrigger = false;

  // If it's know already, no need for the trigger
  if (areEqual(predicate, d_true)) {
    d_notify.eqNotifyTriggerPredicate(predicate, true);
    skipTrigger = true;
  }
  if (areEqual(predicate, d_false)) {
    d_notify.eqNotifyTriggerPredicate(predicate, false);
    skipTrigger = true;
  }

  if (skipTrigger) {
    return;
  }

  // Positive trigger
  addTriggerEqualityInternal(predicate, d_true, predicate, true);
  // Negative trigger
  addTriggerEqualityInternal(predicate, d_false, predicate, false);
}

void EqualityEngine::addTriggerEqualityInternal(TNode t1, TNode t2, TNode trigger, bool polarity) {

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << ", " << t2 << ", " << trigger << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  if (d_done) {
    return;
  }

  // Get the information about t1
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t1classId = getEqualityNode(t1Id).getFind();
  // We will attach it to the class representative, since then we know how to backtrack it
  TriggerId t1TriggerId = d_nodeTriggers[t1classId];

  // Get the information about t2
  EqualityNodeId t2Id = getNodeId(t2);
  EqualityNodeId t2classId = getEqualityNode(t2Id).getFind();
  // We will attach it to the class representative, since then we know how to backtrack it
  TriggerId t2TriggerId = d_nodeTriggers[t2classId];

  Debug("equality") << "EqualityEngine::addTrigger(" << trigger << "): " << t1Id << " (" << t1classId << ") = " << t2Id << " (" << t2classId << ")" << std::endl;

  // Create the triggers
  TriggerId t1NewTriggerId = d_equalityTriggers.size();
  d_equalityTriggers.push_back(Trigger(t1classId, t1TriggerId));
  d_equalityTriggersOriginal.push_back(TriggerInfo(trigger, polarity));
  TriggerId t2NewTriggerId = d_equalityTriggers.size();
  d_equalityTriggers.push_back(Trigger(t2classId, t2TriggerId));
  d_equalityTriggersOriginal.push_back(TriggerInfo(trigger, polarity));

  // Update the counters
  d_equalityTriggersCount = d_equalityTriggers.size();
  Assert(d_equalityTriggers.size() == d_equalityTriggersOriginal.size());
  Assert(d_equalityTriggers.size() % 2 == 0);

  // Add the trigger to the trigger graph
  d_nodeTriggers[t1classId] = t1NewTriggerId;
  d_nodeTriggers[t2classId] = t2NewTriggerId;

  if (Debug.isOn("equality::internal")) {
    debugPrintGraph();
  }

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << "," << t2 << ") => (" << t1NewTriggerId << ", " << t2NewTriggerId << ")" << std::endl;
}

void EqualityEngine::propagate() {

  Debug("equality") << "EqualityEngine::propagate()" << std::endl;

  while (!d_propagationQueue.empty()) {

    // The current merge candidate
    const MergeCandidate current = d_propagationQueue.front();
    d_propagationQueue.pop();

    if (d_done) {
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

    // Add the actual equality to the equality graph
    addGraphEdge(current.t1Id, current.t2Id, current.type, current.reason);

    // One more equality added
    d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;

    // Depending on the merge preference (such as size, or being a constant), merge them
    std::vector<TriggerId> triggers;
    if (node2.getSize() > node1.getSize() || d_isConstant[t2classId]) {
      Debug("equality") << "EqualityEngine::propagate(): merging " << d_nodes[current.t1Id]<< " into " << d_nodes[current.t2Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t2classId, t1classId));
      if (!merge(node2, node1, triggers)) {
        d_done = true;
      }
    } else {
      Debug("equality") << "EqualityEngine::propagate(): merging " << d_nodes[current.t2Id] << " into " << d_nodes[current.t1Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t1classId, t2classId));
      if (!merge(node1, node2, triggers)) {
        d_done = true;
      }
    }

    // Notify the triggers
    if (d_performNotify && !d_done) {
      for (size_t trigger_i = 0, trigger_end = triggers.size(); trigger_i < trigger_end && !d_done; ++ trigger_i) {
        const TriggerInfo& triggerInfo = d_equalityTriggersOriginal[triggers[trigger_i]];
        // Notify the trigger and exit if it fails
        if (triggerInfo.trigger.getKind() == kind::EQUAL) {
          if (!d_notify.eqNotifyTriggerEquality(triggerInfo.trigger, triggerInfo.polarity)) {
            d_done = true;
          }
        } else {
          if (!d_notify.eqNotifyTriggerPredicate(triggerInfo.trigger, triggerInfo.polarity)) {
            d_done = true;
          }
        }
      }
    }
  }
}

void EqualityEngine::debugPrintGraph() const {
  for (EqualityNodeId nodeId = 0; nodeId < d_nodes.size(); ++ nodeId) {

    Debug("equality::graph") << d_nodes[nodeId] << " " << nodeId << "(" << getEqualityNode(nodeId).getFind() << "):";

    EqualityEdgeId edgeId = d_equalityGraph[nodeId];
    while (edgeId != null_edge) {
      const EqualityEdge& edge = d_equalityEdges[edgeId];
      Debug("equality::graph") << " " << d_nodes[edge.getNodeId()] << ":" << edge.getReason();
      edgeId = edge.getNext();
    }

    Debug("equality::graph") << std::endl;
  }
}

bool EqualityEngine::areEqual(TNode t1, TNode t2) const {
  Debug("equality") << "EqualityEngine::areEqual(" << t1 << "," << t2 << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  return getEqualityNode(t1).getFind() == getEqualityNode(t2).getFind();
}

bool EqualityEngine::areDisequal(TNode t1, TNode t2, bool ensureProof) const
{
  Debug("equality") << "EqualityEngine::areDisequal(" << t1 << "," << t2 << ")" << std::endl;

  // Add the terms
  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Get ids
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);

  // Get equivalence classes
  EqualityNodeId t1ClassId = getEqualityNode(t1Id).getFind();
  EqualityNodeId t2ClassId = getEqualityNode(t2Id).getFind();

  // We are semantically const, for remembering stuff
  EqualityEngine* nonConst = const_cast<EqualityEngine*>(this);

  // Check for constants
  if (d_isConstant[t1ClassId] && d_isConstant[t2ClassId] && t1ClassId != t2ClassId) {
    if (ensureProof) {
      nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t1Id, t1ClassId));
      nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t2Id, t2ClassId));
      storePropagatedDisequality(t1, t2, 2);
    }
    return true;
  }

  // Check the equality itself if it exists
  Node eq = t1.eqNode(t2);
  if (hasTerm(eq)) {
    if (getEqualityNode(eq).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(getNodeId(eq), d_falseId));
        storePropagatedDisequality(t1, t2, 1);
      }
      return true;
    }
  }
 
  // Check the other equality itself if it exists
  eq = t2.eqNode(t1);
  if (hasTerm(eq)) {
    if (getEqualityNode(eq).getFind() == getEqualityNode(d_false).getFind()) {
      if (ensureProof) {
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(getNodeId(eq), d_falseId));
        storePropagatedDisequality(t1, t2, 1);
      }
      return true;
    }
  }
  
  // Create the equality
  FunctionApplication eqNormalized(true, t1ClassId, t2ClassId);
  ApplicationIdsMap::const_iterator find = d_applicationLookup.find(eqNormalized);
  if (find != d_applicationLookup.end()) {
    if (getEqualityNode(find->second).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        const FunctionApplication original = d_applications[find->second].original;
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t1Id, original.a));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t2Id, original.b));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.a, t1ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.b, t2ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(find->second, d_falseId));
        storePropagatedDisequality(t1, t2, 5);
      }
      return true;
    }
  }
  
  // Check the symmetric disequality
  std::swap(eqNormalized.a, eqNormalized.b);
  find = d_applicationLookup.find(eqNormalized);
  if (find != d_applicationLookup.end()) {
    if (getEqualityNode(find->second).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        const FunctionApplication original = d_applications[find->second].original;
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t2Id, original.a));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(t1Id, original.b));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.a, t2ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(original.b, t1ClassId));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(find->second, d_falseId));
        storePropagatedDisequality(t1, t2, 5);
      }
      return true;
    }
  }
    
  // Couldn't deduce dis-equalityReturn whether the terms are disequal
  return false;
}

size_t EqualityEngine::getSize(TNode t)
{
  // Add the term
  addTerm(t);
  return getEqualityNode(getEqualityNode(t).getFind()).getSize();
}

void EqualityEngine::addTriggerTerm(TNode t, TheoryId tag)
{
  Debug("equality::internal") << "EqualityEngine::addTriggerTerm(" << t << ", " << tag << ")" << std::endl;
  Assert(tag != THEORY_LAST);

  if (d_done) {
    return;
  }

  // Add the term if it's not already there
  addTerm(t);

  // Get the node id
  EqualityNodeId eqNodeId = getNodeId(t);
  EqualityNode& eqNode = getEqualityNode(eqNodeId);
  EqualityNodeId classId = eqNode.getFind();

  // Possibly existing set of triggers
  TriggerTermSetRef triggerSetRef = d_nodeIndividualTrigger[classId];
  if (triggerSetRef != +null_set_id && getTriggerTermSet(triggerSetRef).hasTrigger(tag)) {
    // If the term already is in the equivalence class that a tagged representative, just notify
    if (d_performNotify) {
      EqualityNodeId triggerId = getTriggerTermSet(triggerSetRef).getTrigger(tag);
      if (!d_notify.eqNotifyTriggerTermEquality(tag, t, d_nodes[triggerId], true)) {
        d_done = true;
      }
    }
  } else {

    // Setup the data for the new set
    if (triggerSetRef != null_set_id) {
      // Get the existing set
      TriggerTermSet& triggerSet = getTriggerTermSet(triggerSetRef);
      // Initialize the new set for copy/insert
      d_newSetTags = Theory::setInsert(tag, triggerSet.tags);
      d_newSetTriggersSize = 0;
      // Copy into to new one, and insert the new tag/id      
      unsigned i = 0;
      Theory::Set tags = d_newSetTags;
      TheoryId current; 
      while ((current = Theory::setPop(tags)) != THEORY_LAST) {
        // Remove from the tags
        tags = Theory::setRemove(current, tags);
        // Insert the id into the triggers
        d_newSetTriggers[d_newSetTriggersSize++] = 
          current == tag ? eqNodeId : triggerSet.triggers[i++];
      }
    } else {
      // Setup a singleton 
      d_newSetTags = Theory::setInsert(tag);
      d_newSetTriggers[0] = eqNodeId;
      d_newSetTriggersSize = 1;
    }

    // Add it to the list for backtracking
    d_triggerTermSetUpdates.push_back(TriggerSetUpdate(classId, triggerSetRef));
    d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
    // Mark the the new set as a trigger 
    d_nodeIndividualTrigger[classId] = newTriggerTermSet();
  }
}

bool EqualityEngine::isTriggerTerm(TNode t, TheoryId tag) const {
  if (!hasTerm(t)) return false;
  EqualityNodeId classId = getEqualityNode(t).getFind();
  TriggerTermSetRef triggerSetRef = d_nodeIndividualTrigger[classId];
  return triggerSetRef != +null_set_id && getTriggerTermSet(triggerSetRef).hasTrigger(tag);
}


TNode EqualityEngine::getTriggerTermRepresentative(TNode t, TheoryId tag) const {
  Assert(isTriggerTerm(t, tag));
  EqualityNodeId classId = getEqualityNode(t).getFind();
  const TriggerTermSet& triggerSet = getTriggerTermSet(d_nodeIndividualTrigger[classId]);
  unsigned i = 0;
  Theory::Set tags = triggerSet.tags;
  while (Theory::setPop(tags) != tag) {
    ++ i;
  }
  return d_nodes[triggerSet.triggers[i]];
}

void EqualityEngine::storeApplicationLookup(FunctionApplication& funNormalized, EqualityNodeId funId) {
  Assert(d_applicationLookup.find(funNormalized) == d_applicationLookup.end());
  d_applicationLookup[funNormalized] = funId;
  d_applicationLookups.push_back(funNormalized);
  d_applicationLookupsCount = d_applicationLookupsCount + 1;
  Debug("equality::backtrack") << "d_applicationLookupsCount = " << d_applicationLookupsCount << std::endl;
  Debug("equality::backtrack") << "d_applicationLookups.size() = " << d_applicationLookups.size() << std::endl;
  Assert(d_applicationLookupsCount == d_applicationLookups.size());
}

void EqualityEngine::getUseListTerms(TNode t, std::set<TNode>& output) {
  if (hasTerm(t)) {
    // Get the equivalence class
    EqualityNodeId classId = getEqualityNode(t).getFind();
    // Go through the equivalence class and get where t is used in
    EqualityNodeId currentId = classId;
    do {
      // Get the current node
      EqualityNode& currentNode = getEqualityNode(currentId);
      // Go through the use-list
      UseListNodeId currentUseId = currentNode.getUseList<USE_LIST_FUNCTIONS>();
      while (currentUseId != null_uselist_id) {
        // Get the node of the use list
        UseListNode& useNode = d_useListNodes[currentUseId];
        // Get the function application
        EqualityNodeId funId = useNode.getApplicationId();
        output.insert(d_nodes[funId]);
        // Go to the next one in the use list
        currentUseId = useNode.getNext();
      }
      // Move to the next node
      currentId = currentNode.getNext();
    } while (currentId != classId);
  }
}

EqualityEngine::TriggerTermSetRef EqualityEngine::newTriggerTermSet() {
  // Size of the required set
  size_t size = sizeof(TriggerTermSet) + d_newSetTriggersSize*sizeof(EqualityNodeId);
  // Align the size
  size = (size + 7) & ~((size_t)7);
  // Reallocate if necessary
  if (d_triggerDatabaseSize + size > d_triggerDatabaseAllocatedSize) {
    d_triggerDatabaseAllocatedSize *= 2;
    d_triggerDatabase = (char*) realloc(d_triggerDatabase, d_triggerDatabaseAllocatedSize);
  }
  // New reference
  TriggerTermSetRef newTriggerSetRef = d_triggerDatabaseSize;
  // Update the size
  d_triggerDatabaseSize = d_triggerDatabaseSize + size;
  // Copy the information
  TriggerTermSet& newSet = getTriggerTermSet(newTriggerSetRef);
  newSet.tags = d_newSetTags;
  for (unsigned i = 0; i < d_newSetTriggersSize; ++i) {
    newSet.triggers[i] = d_newSetTriggers[i];
  }
  // Return the new reference
  return newTriggerSetRef;
}

bool EqualityEngine::storePropagatedDisequality(TNode lhs, TNode rhs, unsigned reasonsCount) const {

  Assert(reasonsCount > 0);


  EqualityNodeId lhsId = getNodeId(lhs);
  EqualityNodeId rhsId = getNodeId(rhs);

  // We are semantically const, just remembering stuff for later
  EqualityEngine* nonConst = const_cast<EqualityEngine*>(this);

  Assert(d_deducedDisequalityReasons.size() >= reasonsCount);
  DisequalityReasonRef ref(d_deducedDisequalityReasons.size() - reasonsCount, d_deducedDisequalityReasons.size());

#ifdef CVC4_ASSERTIONS
  for (unsigned i = ref.mergesStart; i < ref.mergesEnd; ++ i) {
    Assert(getEqualityNode(d_deducedDisequalityReasons[i].first).getFind() == getEqualityNode(d_deducedDisequalityReasons[i].second).getFind());
  }
#endif

  EqualityPair pair(lhsId, rhsId);
  DisequalityReasonsMap::const_iterator find = d_disequalityReasonsMap.find(pair);
  if (find == d_disequalityReasonsMap.end()) {
    nonConst->d_disequalityReasonsMap[pair] = ref;
    nonConst->d_deducedDisequalities.push_back(pair);
    nonConst->d_deducedDisequalitiesSize = d_deducedDisequalities.size();
    std::swap(pair.first, pair.second);
    nonConst->d_disequalityReasonsMap[pair] = ref;
    return true;
  } else {
    nonConst->d_deducedDisequalities.resize(d_deducedDisequalitiesSize);
    return false;
  }
}


} // Namespace uf
} // Namespace theory
} // Namespace CVC4

