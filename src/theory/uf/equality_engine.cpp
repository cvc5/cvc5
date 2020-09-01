/*********************                                                        */
/*! \file equality_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/uf/equality_engine.h"

#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace eq {

EqualityEngine::Statistics::Statistics(std::string name)
    : d_mergesCount(name + "::mergesCount", 0),
      d_termsCount(name + "::termsCount", 0),
      d_functionTermsCount(name + "::functionTermsCount", 0),
      d_constantTermsCount(name + "::constantTermsCount", 0)
{
  smtStatisticsRegistry()->registerStat(&d_mergesCount);
  smtStatisticsRegistry()->registerStat(&d_termsCount);
  smtStatisticsRegistry()->registerStat(&d_functionTermsCount);
  smtStatisticsRegistry()->registerStat(&d_constantTermsCount);
}

EqualityEngine::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_mergesCount);
  smtStatisticsRegistry()->unregisterStat(&d_termsCount);
  smtStatisticsRegistry()->unregisterStat(&d_functionTermsCount);
  smtStatisticsRegistry()->unregisterStat(&d_constantTermsCount);
}

/**
 * Data used in the BFS search through the equality graph.
 */
struct BfsData {
  // The current node
  EqualityNodeId d_nodeId;
  // The index of the edge we traversed
  EqualityEdgeId d_edgeId;
  // Index in the queue of the previous node. Shouldn't be too much of them, at most the size
  // of the biggest equivalence class
  size_t d_previousIndex;

  BfsData(EqualityNodeId nodeId = null_id,
          EqualityEdgeId edgeId = null_edge,
          size_t prev = 0)
      : d_nodeId(nodeId), d_edgeId(edgeId), d_previousIndex(prev)
  {
  }
};

class ScopedBool {
  bool& d_watch;
  bool d_oldValue;

 public:
  ScopedBool(bool& watch, bool newValue) : d_watch(watch), d_oldValue(watch)
  {
    d_watch = newValue;
  }
  ~ScopedBool() { d_watch = d_oldValue; }
};

EqualityEngineNotifyNone EqualityEngine::s_notifyNone;

void EqualityEngine::init() {
  Debug("equality") << "EqualityEdge::EqualityEngine(): id_null = " << +null_id << std::endl;
  Debug("equality") << "EqualityEdge::EqualityEngine(): edge_null = " << +null_edge << std::endl;
  Debug("equality") << "EqualityEdge::EqualityEngine(): trigger_null = " << +null_trigger << std::endl;

  // If we are not at level zero when we initialize this equality engine, we
  // may remove true/false from the equality engine when we pop to level zero,
  // which leads to issues.
  Assert(d_context->getLevel() == 0);

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  d_triggerDatabaseAllocatedSize = 100000;
  d_triggerDatabase = (char*) malloc(d_triggerDatabaseAllocatedSize);

  //We can't notify during the initialization because it notifies
  // QuantifiersEngine.AddTermToDatabase that try to access to the uf
  // instantiator that currently doesn't exist.
  ScopedBool sb(d_performNotify, false);
  addTermInternal(d_true);
  addTermInternal(d_false);

  d_trueId = getNodeId(d_true);
  d_falseId = getNodeId(d_false);

  d_freshMergeReasonType = eq::NUMBER_OF_MERGE_REASONS;
}

EqualityEngine::~EqualityEngine() {
  free(d_triggerDatabase);
}

EqualityEngine::EqualityEngine(context::Context* context,
                               std::string name,
                               bool constantsAreTriggers,
                               bool anyTermTriggers)
    : ContextNotifyObj(context),
      d_masterEqualityEngine(0),
      d_context(context),
      d_done(context, false),
      d_performNotify(true),
      d_notify(s_notifyNone),
      d_applicationLookupsCount(context, 0),
      d_nodesCount(context, 0),
      d_assertedEqualitiesCount(context, 0),
      d_equalityTriggersCount(context, 0),
      d_subtermEvaluatesSize(context, 0),
      d_stats(name),
      d_inPropagate(false),
      d_constantsAreTriggers(constantsAreTriggers),
      d_anyTermsAreTriggers(anyTermTriggers),
      d_triggerDatabaseSize(context, 0),
      d_triggerTermSetUpdatesSize(context, 0),
      d_deducedDisequalitiesSize(context, 0),
      d_deducedDisequalityReasonsSize(context, 0),
      d_propagatedDisequalities(context),
      d_name(name)
{
  init();
}

EqualityEngine::EqualityEngine(EqualityEngineNotify& notify,
                               context::Context* context,
                               std::string name,
                               bool constantsAreTriggers,
                               bool anyTermTriggers)
    : ContextNotifyObj(context),
      d_masterEqualityEngine(0),
      d_context(context),
      d_done(context, false),
      d_performNotify(true),
      d_notify(notify),
      d_applicationLookupsCount(context, 0),
      d_nodesCount(context, 0),
      d_assertedEqualitiesCount(context, 0),
      d_equalityTriggersCount(context, 0),
      d_subtermEvaluatesSize(context, 0),
      d_stats(name),
      d_inPropagate(false),
      d_constantsAreTriggers(constantsAreTriggers),
      d_anyTermsAreTriggers(anyTermTriggers),
      d_triggerDatabaseSize(context, 0),
      d_triggerTermSetUpdatesSize(context, 0),
      d_deducedDisequalitiesSize(context, 0),
      d_deducedDisequalityReasonsSize(context, 0),
      d_propagatedDisequalities(context),
      d_name(name)
{
  init();
}

void EqualityEngine::setMasterEqualityEngine(EqualityEngine* master) {
  Assert(d_masterEqualityEngine == 0);
  d_masterEqualityEngine = master;
}

void EqualityEngine::enqueue(const MergeCandidate& candidate, bool back) {
  Debug("equality") << d_name << "::eq::enqueue({" << candidate.d_t1Id << "} "
                    << d_nodes[candidate.d_t1Id] << ", {" << candidate.d_t2Id
                    << "} " << d_nodes[candidate.d_t2Id] << ", "
                    << static_cast<MergeReasonType>(candidate.d_type)
                    << "). reason: " << candidate.d_reason << std::endl;
  if (back) {
    d_propagationQueue.push_back(candidate);
  } else {
    d_propagationQueue.push_front(candidate);
  }
}

EqualityNodeId EqualityEngine::newApplicationNode(TNode original, EqualityNodeId t1, EqualityNodeId t2, FunctionApplicationType type) {
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original
                    << ", {" << t1 << "} " << d_nodes[t1] << ", {" << t2 << "} "
                    << d_nodes[t2] << ")" << std::endl;

  ++d_stats.d_functionTermsCount;

  // Get another id for this
  EqualityNodeId funId = newNode(original);
  FunctionApplication funOriginal(type, t1, t2);
  // The function application we're creating
  EqualityNodeId t1ClassId = getEqualityNode(t1).getFind();
  EqualityNodeId t2ClassId = getEqualityNode(t2).getFind();
  FunctionApplication funNormalized(type, t1ClassId, t2ClassId);

  Debug("equality") << d_name << "::eq::newApplicationNode: funOriginal: ("
                    << type << " " << d_nodes[t1] << " " << d_nodes[t2]
                    << "), funNorm: (" << type << " " << d_nodes[t1ClassId]
                    << " " << d_nodes[t2ClassId] << ")\n";

  // We add the original version
  d_applications[funId] = FunctionApplicationPair(funOriginal, funNormalized);

  // Add the lookup data, if it's not already there
  ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
  if (find == d_applicationLookup.end()) {
    Debug("equality") << d_name << "::eq::newApplicationNode(" << original
                      << ", " << t1 << ", " << t2
                      << "): no lookup, setting up funNorm: (" << type << " "
                      << d_nodes[t1ClassId] << " " << d_nodes[t2ClassId]
                      << ") => " << funId << std::endl;
    // Mark the normalization to the lookup
    storeApplicationLookup(funNormalized, funId);
  } else {
    // If it's there, we need to merge these two
    Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): lookup exists, adding to queue" << std::endl;
    Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): lookup = " << d_nodes[find->second] << std::endl;
    enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
  }

  // Add to the use lists
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): adding " << original << " to the uselist of " << d_nodes[t1] << std::endl;
  d_equalityNodes[t1].usedIn(funId, d_useListNodes);
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << "): adding " << original << " to the uselist of " << d_nodes[t2] << std::endl;
  d_equalityNodes[t2].usedIn(funId, d_useListNodes);

  // Return the new id
  Debug("equality") << d_name << "::eq::newApplicationNode(" << original << ", " << t1 << ", " << t2 << ") => " << funId << std::endl;

  return funId;
}

EqualityNodeId EqualityEngine::newNode(TNode node) {

  Debug("equality") << d_name << "::eq::newNode(" << node << ")" << std::endl;

  ++d_stats.d_termsCount;

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
  d_isConstant.push_back(false);
  // No terms to evaluate by defaul
  d_subtermsToEvaluate.push_back(0);
  // Mark equality nodes
  d_isEquality.push_back(false);
  // Mark the node as internal by default
  d_isInternal.push_back(true);
  // Add the equality node to the nodes
  d_equalityNodes.push_back(EqualityNode(newId));

  // Increase the counters
  d_nodesCount = d_nodesCount + 1;

  Debug("equality") << d_name << "::eq::newNode(" << node << ") => " << newId << std::endl;

  return newId;
}

void EqualityEngine::addFunctionKind(Kind fun, bool interpreted, bool extOperator) {
  d_congruenceKinds |= fun;
  if (fun != kind::EQUAL) {
    if (interpreted) {
      Debug("equality::evaluation") << d_name << "::eq::addFunctionKind(): " << fun << " is interpreted " << std::endl;
      d_congruenceKindsInterpreted |= fun;
    }
    if (extOperator) {
      Debug("equality::extoperator") << d_name << "::eq::addFunctionKind(): " << fun << " is an external operator kind " << std::endl;
      d_congruenceKindsExtOperators |= fun;
    }
  }
}

void EqualityEngine::subtermEvaluates(EqualityNodeId id)  {
  Debug("equality::evaluation") << d_name << "::eq::subtermEvaluates(" << d_nodes[id] << "): " << d_subtermsToEvaluate[id] << std::endl;
  Assert(!d_isInternal[id]);
  Assert(d_subtermsToEvaluate[id] > 0);
  if ((-- d_subtermsToEvaluate[id]) == 0) {
    d_evaluationQueue.push(id);
  }
  d_subtermEvaluates.push_back(id);
  d_subtermEvaluatesSize = d_subtermEvaluates.size();
  Debug("equality::evaluation") << d_name << "::eq::subtermEvaluates(" << d_nodes[id] << "): new " << d_subtermsToEvaluate[id] << std::endl;
}

void EqualityEngine::addTermInternal(TNode t, bool isOperator) {

  Debug("equality") << d_name << "::eq::addTermInternal(" << t << ")" << std::endl;

  // If there already, we're done
  if (hasTerm(t)) {
    Debug("equality") << d_name << "::eq::addTermInternal(" << t << "): already there" << std::endl;
    return;
  }

  if (d_done) {
    return;
  }

  EqualityNodeId result;

  Kind tk = t.getKind();
  if (tk == kind::EQUAL)
  {
    addTermInternal(t[0]);
    addTermInternal(t[1]);
    EqualityNodeId t0id = getNodeId(t[0]);
    EqualityNodeId t1id = getNodeId(t[1]);
    result = newApplicationNode(t, t0id, t1id, APP_EQUALITY);
    d_isInternal[result] = false;
    d_isConstant[result] = false;
  }
  else if (t.getNumChildren() > 0 && d_congruenceKinds[tk])
  {
    TNode tOp = t.getOperator();
    // Add the operator
    addTermInternal(tOp, !isExternalOperatorKind(tk));
    result = getNodeId(tOp);
    // Add all the children and Curryfy
    bool isInterpreted = isInterpretedFunctionKind(tk);
    for (unsigned i = 0; i < t.getNumChildren(); ++ i) {
      // Add the child
      addTermInternal(t[i]);
      EqualityNodeId tiId = getNodeId(t[i]);
      // Add the application
      result = newApplicationNode(t, result, tiId, isInterpreted ? APP_INTERPRETED : APP_UNINTERPRETED);
    }
    d_isInternal[result] = false;
    d_isConstant[result] = t.isConst();
    // If interpreted, set the number of non-interpreted children
    if (isInterpreted) {
      // How many children are not constants yet
      d_subtermsToEvaluate[result] = t.getNumChildren();
      for (unsigned i = 0; i < t.getNumChildren(); ++ i) {
        if (isConstant(getNodeId(t[i]))) {
          Debug("equality::evaluation") << d_name << "::eq::addTermInternal(" << t << "): evaluates " << t[i] << std::endl;
          subtermEvaluates(result);
        }
      }
    }
  }
  else
  {
    // Otherwise we just create the new id
    result = newNode(t);
    // Is this an operator
    d_isInternal[result] = isOperator;
    d_isConstant[result] = !isOperator && t.isConst();
  }

  if (tk == kind::EQUAL)
  {
    // We set this here as this only applies to actual terms, not the
    // intermediate application terms
    d_isEquality[result] = true;
  }
  else
  {
    // Notify e.g. the theory that owns this equality engine that there is a
    // new equivalence class.
    if (d_performNotify)
    {
      d_notify.eqNotifyNewClass(t);
    }
    if (d_constantsAreTriggers && d_isConstant[result])
    {
      // Non-Boolean constants are trigger terms for all tags
      EqualityNodeId tId = getNodeId(t);
      // Setup the new set
      TheoryIdSet newSetTags = 0;
      EqualityNodeId newSetTriggers[THEORY_LAST];
      unsigned newSetTriggersSize = THEORY_LAST;
      for (TheoryId currentTheory = THEORY_FIRST; currentTheory != THEORY_LAST;
           ++currentTheory)
      {
        newSetTags = TheoryIdSetUtil::setInsert(currentTheory, newSetTags);
        newSetTriggers[currentTheory] = tId;
      }
      // Add it to the list for backtracking
      d_triggerTermSetUpdates.push_back(TriggerSetUpdate(tId, null_set_id));
      d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
      // Mark the the new set as a trigger
      d_nodeIndividualTrigger[tId] =
          newTriggerTermSet(newSetTags, newSetTriggers, newSetTriggersSize);
    }
  }

  // If this is not an internal node, add it to the master
  if (d_masterEqualityEngine && !d_isInternal[result]) {
    d_masterEqualityEngine->addTermInternal(t);
  }

  // Empty the queue
  propagate();

  Assert(hasTerm(t));

  Debug("equality") << d_name << "::eq::addTermInternal(" << t << ") => " << result << std::endl;
}

bool EqualityEngine::hasTerm(TNode t) const {
  return d_nodeIds.find(t) != d_nodeIds.end();
}

EqualityNodeId EqualityEngine::getNodeId(TNode node) const {
  Assert(hasTerm(node)) << node;
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

void EqualityEngine::assertEqualityInternal(TNode t1, TNode t2, TNode reason, unsigned pid) {
  Debug("equality") << d_name << "::eq::addEqualityInternal(" << t1 << "," << t2
                    << "), reason = " << reason
                    << ", pid = " << static_cast<MergeReasonType>(pid)
                    << std::endl;

  if (d_done) {
    return;
  }

  // Add the terms if they are not already in the database
  addTermInternal(t1);
  addTermInternal(t2);

  // Add to the queue and propagate
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);
  enqueue(MergeCandidate(t1Id, t2Id, pid, reason));
}

bool EqualityEngine::assertPredicate(TNode t,
                                     bool polarity,
                                     TNode reason,
                                     unsigned pid)
{
  Debug("equality") << d_name << "::eq::addPredicate(" << t << "," << (polarity ? "true" : "false") << ")" << std::endl;
  Assert(t.getKind() != kind::EQUAL) << "Use assertEquality instead";
  TNode b = polarity ? d_true : d_false;
  if (hasTerm(t) && areEqual(t, b))
  {
    return false;
  }
  assertEqualityInternal(t, b, reason, pid);
  propagate();
  return true;
}

bool EqualityEngine::assertEquality(TNode eq,
                                    bool polarity,
                                    TNode reason,
                                    unsigned pid)
{
  Debug("equality") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ")" << std::endl;
  if (polarity) {
    // If two terms are already equal, don't assert anything
    if (hasTerm(eq[0]) && hasTerm(eq[1]) && areEqual(eq[0], eq[1])) {
      return false;
    }
    // Add equality between terms
    assertEqualityInternal(eq[0], eq[1], reason, pid);
    propagate();
  } else {
    // If two terms are already dis-equal, don't assert anything
    if (hasTerm(eq[0]) && hasTerm(eq[1]) && areDisequal(eq[0], eq[1], false)) {
      return false;
    }

    // notify the theory
    if (d_performNotify) {
      d_notify.eqNotifyDisequal(eq[0], eq[1], reason);
    }

    Debug("equality::trigger") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ")" << std::endl;

    assertEqualityInternal(eq, d_false, reason, pid);
    propagate();

    if (d_done) {
      return true;
    }

    // If both have constant representatives, we don't notify anyone
    EqualityNodeId a = getNodeId(eq[0]);
    EqualityNodeId b = getNodeId(eq[1]);
    EqualityNodeId aClassId = getEqualityNode(a).getFind();
    EqualityNodeId bClassId = getEqualityNode(b).getFind();
    if (d_isConstant[aClassId] && d_isConstant[bClassId]) {
      return true;
    }

    // If we are adding a disequality, notify of the shared term representatives
    EqualityNodeId eqId = getNodeId(eq);
    TriggerTermSetRef aTriggerRef = d_nodeIndividualTrigger[aClassId];
    TriggerTermSetRef bTriggerRef = d_nodeIndividualTrigger[bClassId];
    if (aTriggerRef != +null_set_id && bTriggerRef != +null_set_id) {
      Debug("equality::trigger") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ": have triggers" << std::endl;
      // The sets of trigger terms
      TriggerTermSet& aTriggerTerms = getTriggerTermSet(aTriggerRef);
      TriggerTermSet& bTriggerTerms = getTriggerTermSet(bTriggerRef);
      // Go through and notify the shared dis-equalities
      TheoryIdSet aTags = aTriggerTerms.d_tags;
      TheoryIdSet bTags = bTriggerTerms.d_tags;
      TheoryId aTag = TheoryIdSetUtil::setPop(aTags);
      TheoryId bTag = TheoryIdSetUtil::setPop(bTags);
      int a_i = 0, b_i = 0;
      while (aTag != THEORY_LAST && bTag != THEORY_LAST) {
        if (aTag < bTag) {
          aTag = TheoryIdSetUtil::setPop(aTags);
          ++ a_i;
        } else if (aTag > bTag) {
          bTag = TheoryIdSetUtil::setPop(bTags);
          ++ b_i;
        } else {
          // Same tags, notify
          EqualityNodeId aSharedId = aTriggerTerms.d_triggers[a_i++];
          EqualityNodeId bSharedId = bTriggerTerms.d_triggers[b_i++];
          // Propagate
          if (!hasPropagatedDisequality(aTag, aSharedId, bSharedId)) {
            // Store a proof if not there already
            if (!hasPropagatedDisequality(aSharedId, bSharedId)) {
              d_deducedDisequalityReasons.push_back(EqualityPair(aSharedId, a));
              d_deducedDisequalityReasons.push_back(EqualityPair(bSharedId, b));
              d_deducedDisequalityReasons.push_back(EqualityPair(eqId, d_falseId));
            }
            // Store the propagation
            storePropagatedDisequality(aTag, aSharedId, bSharedId);
            // Notify
            Debug("equality::trigger") << d_name << "::eq::addEquality(" << eq << "," << (polarity ? "true" : "false") << ": notifying " << aTag << " for " << d_nodes[aSharedId] << " != " << d_nodes[bSharedId] << std::endl;
            if (!d_notify.eqNotifyTriggerTermEquality(aTag, d_nodes[aSharedId], d_nodes[bSharedId], false)) {
              break;
            }
          }
          // Pop the next tags
          aTag = TheoryIdSetUtil::setPop(aTags);
          bTag = TheoryIdSetUtil::setPop(bTags);
        }
      }
    }
  }
  return true;
}

TNode EqualityEngine::getRepresentative(TNode t) const {
  Debug("equality::internal") << d_name << "::eq::getRepresentative(" << t << ")" << std::endl;
  Assert(hasTerm(t));
  EqualityNodeId representativeId = getEqualityNode(t).getFind();
  Assert(!d_isInternal[representativeId]);
  Debug("equality::internal") << d_name << "::eq::getRepresentative(" << t << ") => " << d_nodes[representativeId] << std::endl;
  return d_nodes[representativeId];
}

bool EqualityEngine::merge(EqualityNode& class1, EqualityNode& class2, std::vector<TriggerId>& triggersFired) {

  Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << ")" << std::endl;

  Assert(triggersFired.empty());

  ++d_stats.d_mergesCount;

  EqualityNodeId class1Id = class1.getFind();
  EqualityNodeId class2Id = class2.getFind();

  Node n1 = d_nodes[class1Id];
  Node n2 = d_nodes[class2Id];
  EqualityNode cc1 = getEqualityNode(n1);
  EqualityNode cc2 = getEqualityNode(n2);
  bool doNotify = false;
  // Determine if we should notify the owner of this class of this merge.
  // The second part of this check is needed due to the internal implementation
  // of this class. It ensures that we are merging terms and not operators.
  if (d_performNotify && class1Id == cc1.getFind() && class2Id == cc2.getFind())
  {
    doNotify = true;
  }

  // Check for constant merges
  bool class1isConstant = d_isConstant[class1Id];
  bool class2isConstant = d_isConstant[class2Id];
  Assert(class1isConstant || !class2isConstant)
      << "Should always merge into constants";
  Assert(!class1isConstant || !class2isConstant) << "Don't merge constants";

  // Trigger set of class 1
  TriggerTermSetRef class1triggerRef = d_nodeIndividualTrigger[class1Id];
  TheoryIdSet class1Tags = class1triggerRef == null_set_id
                               ? 0
                               : getTriggerTermSet(class1triggerRef).d_tags;
  // Trigger set of class 2
  TriggerTermSetRef class2triggerRef = d_nodeIndividualTrigger[class2Id];
  TheoryIdSet class2Tags = class2triggerRef == null_set_id
                               ? 0
                               : getTriggerTermSet(class2triggerRef).d_tags;

  // Disequalities coming from class2
  TaggedEqualitiesSet class2disequalitiesToNotify;
  // Disequalities coming from class1
  TaggedEqualitiesSet class1disequalitiesToNotify;

  // Individual tags
  TheoryIdSet class1OnlyTags =
      TheoryIdSetUtil::setDifference(class1Tags, class2Tags);
  TheoryIdSet class2OnlyTags =
      TheoryIdSetUtil::setDifference(class2Tags, class1Tags);

  // Only get disequalities if they are not both constant
  if (!class1isConstant || !class2isConstant) {
    getDisequalities(!class1isConstant, class2Id, class1OnlyTags, class2disequalitiesToNotify);
    getDisequalities(!class2isConstant, class1Id, class2OnlyTags, class1disequalitiesToNotify);
  }

  // Update class2 representative information
  Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): updating class " << class2Id << std::endl;
  EqualityNodeId currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): " << currentId << "->" << class1Id << std::endl;
    currentNode.setFind(class1Id);

    // Go through the triggers and inform if necessary
    TriggerId currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != null_trigger) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      Trigger& otherTrigger = d_equalityTriggers[currentTrigger ^ 1];

      // If the two are not already in the same class
      if (otherTrigger.d_classId != trigger.d_classId)
      {
        trigger.d_classId = class1Id;
        // If they became the same, call the trigger
        if (otherTrigger.d_classId == class1Id)
        {
          // Id of the real trigger is half the internal one
          triggersFired.push_back(currentTrigger);
        }
      }

      // Go to the next trigger
      currentTrigger = trigger.d_nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Update class2 table lookup and information if not a boolean
  // since booleans can't be in an application
  if (!d_isEquality[class2Id]) {
    Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of " << class2Id << std::endl;
    do {
      // Get the current node
      EqualityNode& currentNode = getEqualityNode(currentId);
      Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): updating lookups of node " << currentId << std::endl;

      // Go through the uselist and check for congruences
      UseListNodeId currentUseId = currentNode.getUseList();
      while (currentUseId != null_uselist_id) {
        // Get the node of the use list
        UseListNode& useNode = d_useListNodes[currentUseId];
        // Get the function application
        EqualityNodeId funId = useNode.getApplicationId();
        Debug("equality") << d_name << "::eq::merge(" << class1.getFind() << "," << class2.getFind() << "): " << d_nodes[currentId] << " in " << d_nodes[funId] << std::endl;
        const FunctionApplication& fun =
            d_applications[useNode.getApplicationId()].d_normalized;
        // If it's interpreted and we can interpret
        if (fun.isInterpreted() && class1isConstant && !d_isInternal[currentId])
        {
          // Get the actual term id
          TNode term = d_nodes[funId];
          subtermEvaluates(getNodeId(term));
        }
        // Check if there is an application with find arguments
        EqualityNodeId aNormalized = getEqualityNode(fun.d_a).getFind();
        EqualityNodeId bNormalized = getEqualityNode(fun.d_b).getFind();
        FunctionApplication funNormalized(fun.d_type, aNormalized, bNormalized);
        ApplicationIdsMap::iterator find = d_applicationLookup.find(funNormalized);
        if (find != d_applicationLookup.end()) {
          // Applications fun and the funNormalized can be merged due to congruence
          if (getEqualityNode(funId).getFind() != getEqualityNode(find->second).getFind()) {
            enqueue(MergeCandidate(funId, find->second, MERGED_THROUGH_CONGRUENCE, TNode::null()));
          }
        } else {
          // There is no representative, so we can add one, we remove this when backtracking
          storeApplicationLookup(funNormalized, funId);
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

  // notify the theory
  if (doNotify) {
    d_notify.eqNotifyMerge(n1, n2);
  }

  // Go through the trigger term disequalities and propagate
  if (!propagateTriggerTermDisequalities(class1OnlyTags, class1triggerRef, class2disequalitiesToNotify)) {
    return false;
  }
  if (!propagateTriggerTermDisequalities(class2OnlyTags, class2triggerRef, class1disequalitiesToNotify)) {
    return false;
  }

  // Notify the trigger term merges
  if (class2triggerRef != +null_set_id) {
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
      TheoryIdSet newSetTags = TheoryIdSetUtil::setUnion(class1triggers.d_tags,
                                                         class2triggers.d_tags);
      EqualityNodeId newSetTriggers[THEORY_LAST];
      unsigned newSetTriggersSize = 0;

      int i1 = 0;
      int i2 = 0;
      TheoryIdSet tags1 = class1triggers.d_tags;
      TheoryIdSet tags2 = class2triggers.d_tags;
      TheoryId tag1 = TheoryIdSetUtil::setPop(tags1);
      TheoryId tag2 = TheoryIdSetUtil::setPop(tags2);

      // Comparing the THEORY_LAST is OK because all other theories are
      // smaller, and will therefore be preferred
      while (tag1 != THEORY_LAST || tag2 != THEORY_LAST)
      {
        if (tag1 < tag2) {
          // copy tag1
          newSetTriggers[newSetTriggersSize++] =
              class1triggers.d_triggers[i1++];
          tag1 = TheoryIdSetUtil::setPop(tags1);
        } else if (tag1 > tag2) {
          // copy tag2
          newSetTriggers[newSetTriggersSize++] =
              class2triggers.d_triggers[i2++];
          tag2 = TheoryIdSetUtil::setPop(tags2);
        } else {
          // copy tag1
          EqualityNodeId tag1id = newSetTriggers[newSetTriggersSize++] =
              class1triggers.d_triggers[i1++];
          // since they are both tagged notify of merge
          if (d_performNotify) {
            EqualityNodeId tag2id = class2triggers.d_triggers[i2++];
            if (!d_notify.eqNotifyTriggerTermEquality(tag1, d_nodes[tag1id], d_nodes[tag2id], true)) {
              return false;
            }
          }
          // Next tags
          tag1 = TheoryIdSetUtil::setPop(tags1);
          tag2 = TheoryIdSetUtil::setPop(tags2);
        }
      }

      // Add the new trigger set, if different from previous one
      if (class1triggers.d_tags != class2triggers.d_tags)
      {
        // Add it to the list for backtracking
        d_triggerTermSetUpdates.push_back(TriggerSetUpdate(class1Id, class1triggerRef));
        d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
        // Mark the the new set as a trigger
        d_nodeIndividualTrigger[class1Id] = newTriggerTermSet(newSetTags, newSetTriggers, newSetTriggersSize);
      }
    }
  }

  // Everything fine
  return true;
}

void EqualityEngine::undoMerge(EqualityNode& class1, EqualityNode& class2, EqualityNodeId class2Id) {

  Debug("equality") << d_name << "::eq::undoMerge(" << class1.getFind() << "," << class2Id << ")" << std::endl;

  // Now unmerge the lists (same as merge)
  class1.merge<false>(class2);

  // Update class2 representative information
  EqualityNodeId currentId = class2Id;
  Debug("equality") << d_name << "::eq::undoMerge(" << class1.getFind() << "," << class2Id << "): undoing representative info" << std::endl;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    currentNode.setFind(class2Id);

    // Go through the trigger list (if any) and undo the class
    TriggerId currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != null_trigger) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      trigger.d_classId = class2Id;
      currentTrigger = trigger.d_nextTrigger;
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
      d_propagationQueue.pop_front();
    }

    Debug("equality") << d_name << "::eq::backtrack(): nodes" << std::endl;

    for (int i = (int)d_assertedEqualities.size() - 1, i_end = (int)d_assertedEqualitiesCount; i >= i_end; --i) {
      // Get the ids of the merged classes
      Equality& eq = d_assertedEqualities[i];
      // Undo the merge
      if (eq.d_lhs != null_id)
      {
        undoMerge(
            d_equalityNodes[eq.d_lhs], d_equalityNodes[eq.d_rhs], eq.d_rhs);
      }
    }

    d_assertedEqualities.resize(d_assertedEqualitiesCount);

    Debug("equality") << d_name << "::eq::backtrack(): edges" << std::endl;

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
      d_nodeIndividualTrigger[update.d_classId] = update.d_oldValue;
    }
    d_triggerTermSetUpdates.resize(d_triggerTermSetUpdatesSize);
  }

  if (d_equalityTriggers.size() > d_equalityTriggersCount) {
    // Unlink the triggers from the lists
    for (int i = d_equalityTriggers.size() - 1, i_end = d_equalityTriggersCount; i >= i_end; -- i) {
      const Trigger& trigger = d_equalityTriggers[i];
      d_nodeTriggers[trigger.d_classId] = trigger.d_nextTrigger;
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

  if (d_subtermEvaluates.size() > d_subtermEvaluatesSize) {
    for(int i = d_subtermEvaluates.size() - 1, i_end = (int)d_subtermEvaluatesSize; i >= i_end; --i) {
      d_subtermsToEvaluate[d_subtermEvaluates[i]] ++;
    }
    d_subtermEvaluates.resize(d_subtermEvaluatesSize);
  }

  if (d_nodes.size() > d_nodesCount) {
    // Go down the nodes, check the application nodes and remove them from use-lists
    for(int i = d_nodes.size() - 1, i_end = (int)d_nodesCount; i >= i_end; -- i) {
      // Remove from the node -> id map
      Debug("equality") << d_name << "::eq::backtrack(): removing node " << d_nodes[i] << std::endl;
      d_nodeIds.erase(d_nodes[i]);

      const FunctionApplication& app = d_applications[i].d_original;
      if (!app.isNull()) {
        // Remove b from use-list
        getEqualityNode(app.d_b).removeTopFromUseList(d_useListNodes);
        // Remove a from use-list
        getEqualityNode(app.d_a).removeTopFromUseList(d_useListNodes);
      }
    }

    // Now get rid of the nodes and the rest
    d_nodes.resize(d_nodesCount);
    d_applications.resize(d_nodesCount);
    d_nodeTriggers.resize(d_nodesCount);
    d_nodeIndividualTrigger.resize(d_nodesCount);
    d_isConstant.resize(d_nodesCount);
    d_subtermsToEvaluate.resize(d_nodesCount);
    d_isEquality.resize(d_nodesCount);
    d_isInternal.resize(d_nodesCount);
    d_equalityGraph.resize(d_nodesCount);
    d_equalityNodes.resize(d_nodesCount);
  }

  if (d_deducedDisequalities.size() > d_deducedDisequalitiesSize) {
    for(int i = d_deducedDisequalities.size() - 1, i_end = (int)d_deducedDisequalitiesSize; i >= i_end; -- i) {
      EqualityPair pair = d_deducedDisequalities[i];
      Assert(d_disequalityReasonsMap.find(pair)
             != d_disequalityReasonsMap.end());
      // Remove from the map
      d_disequalityReasonsMap.erase(pair);
      std::swap(pair.first, pair.second);
      d_disequalityReasonsMap.erase(pair);
    }
    d_deducedDisequalityReasons.resize(d_deducedDisequalityReasonsSize);
    d_deducedDisequalities.resize(d_deducedDisequalitiesSize);
  }

}

void EqualityEngine::addGraphEdge(EqualityNodeId t1, EqualityNodeId t2, unsigned type, TNode reason) {
  Debug("equality") << d_name << "::eq::addGraphEdge({" << t1 << "} "
                    << d_nodes[t1] << ", {" << t2 << "} " << d_nodes[t2] << ","
                    << reason << ")" << std::endl;
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
      out << "{" << edge.getNodeId() << "} " << d_nodes[edge.getNodeId()];
      edgeId = edge.getNext();
      first = false;
    }
  }
  return out.str();
}

void EqualityEngine::buildEqConclusion(EqualityNodeId id1,
                                       EqualityNodeId id2,
                                       EqProof* eqp) const
{
  Kind k1 = d_nodes[id1].getKind();
  Kind k2 = d_nodes[id2].getKind();
  // only try to build if ids do not correspond to internal nodes. If they do,
  // only try to build build if full applications corresponding to the given ids
  // have the same congruence n-ary non-APPLY_UF kind, since the internal nodes
  // may be full nodes.
  if ((d_isInternal[id1] || d_isInternal[id2])
      && (k1 != k2 || k1 == kind::APPLY_UF || !ExprManager::isNAryKind(k1)))
  {
    return;
  }
  Node eq[2];
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0; i < 2; ++i)
  {
    EqualityNodeId equalityNodeId = i == 0 ? id1 : id2;
    Node equalityNode = d_nodes[equalityNodeId];
    // if not an internal node, just retrieve it
    if (!d_isInternal[equalityNodeId])
    {
      eq[i] = equalityNode;
      continue;
    }
    // build node relative to partial application of this
    // n-ary kind. We get the full application, then we get
    // the arguments relative to how partial the internal
    // node is, and build the application

    // get number of children of partial app:
    // #children of full app - (id of full app - id of
    // partial app)
    EqualityNodeId fullAppId = getNodeId(equalityNode);
    EqualityNodeId curr = fullAppId;
    unsigned separation = 0;
    Assert(fullAppId >= equalityNodeId);
    while (curr != equalityNodeId)
    {
      separation = separation + (d_nodes[curr--] == equalityNode ? 1 : 0);
    }
    // compute separation, which is how many ids with the
    // same fullappnode exist between equalityNodeId and
    // fullAppId
    unsigned numChildren = equalityNode.getNumChildren() - separation;
    Assert(numChildren < equalityNode.getNumChildren())
        << "broke for numChildren " << numChildren << ", fullAppId "
        << fullAppId << ", equalityNodeId " << equalityNodeId << ", node "
        << equalityNode << ", cong: {" << id1 << "} " << d_nodes[id1] << " = {"
        << id2 << "} " << d_nodes[id2] << "\n";
    // if has at least as many children as the minimal
    // number of children of the n-ary kind, build the node
    if (numChildren >= ExprManager::minArity(k1))
    {
      std::vector<Node> children;
      for (unsigned j = 0; j < numChildren; ++j)
      {
        children.push_back(equalityNode[j]);
      }
      eq[i] = nm->mkNode(k1, children);
    }
  }
  // if built equality, add it as eqp's conclusion
  if (!eq[0].isNull() && !eq[1].isNull())
  {
    eqp->d_node = eq[0].eqNode(eq[1]);
  }
}

void EqualityEngine::explainEquality(TNode t1, TNode t2, bool polarity,
                                     std::vector<TNode>& equalities,
                                     EqProof* eqp) const {
  Debug("pf::ee") << d_name << "::eq::explainEquality(" << t1 << ", " << t2
                  << ", " << (polarity ? "true" : "false") << ")"
                  << ", proof = " << (eqp ? "ON" : "OFF") << std::endl;

  // The terms must be there already
  Assert(hasTerm(t1) && hasTerm(t2));

  if (Debug.isOn("equality::internal"))
  {
    debugPrintGraph();
  }
  // Get the ids
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);

  std::map<std::pair<EqualityNodeId, EqualityNodeId>, EqProof*> cache;
  if (polarity) {
    // Get the explanation
    getExplanation(t1Id, t2Id, equalities, cache, eqp);
  } else {
    if (eqp) {
      eqp->d_id = eq::MERGED_THROUGH_TRANS;
      eqp->d_node = d_nodes[t1Id].eqNode(d_nodes[t2Id]).notNode();
    }

    // Get the reason for this disequality
    EqualityPair pair(t1Id, t2Id);
    Assert(d_disequalityReasonsMap.find(pair) != d_disequalityReasonsMap.end())
        << "Don't ask for stuff I didn't notify you about";
    DisequalityReasonRef reasonRef = d_disequalityReasonsMap.find(pair)->second;
    if (eqp)
    {
      Debug("pf::ee") << "Deq reason for " << eqp->d_node << " "
                      << reasonRef.d_mergesStart << "..."
                      << reasonRef.d_mergesEnd << std::endl;
    }
    for (unsigned i = reasonRef.d_mergesStart; i < reasonRef.d_mergesEnd; ++i)
    {
      EqualityPair toExplain = d_deducedDisequalityReasons[i];
      std::shared_ptr<EqProof> eqpc;

      // If we're constructing a (transitivity) proof, we don't need to include an explanation for x=x.
      if (eqp && toExplain.first != toExplain.second) {
        eqpc = std::make_shared<EqProof>();
        Debug("pf::ee") << "Deq getExplanation #" << i << " for " << eqp->d_node
                        << " : " << toExplain.first << " " << toExplain.second
                        << std::endl;
      }

      getExplanation(
          toExplain.first, toExplain.second, equalities, cache, eqpc.get());

      if (eqpc) {
        if (Debug.isOn("pf::ee"))
        {
          Debug("pf::ee") << "Child proof is:" << std::endl;
          eqpc->debug_print("pf::ee", 1);
        }
        if (eqpc->d_id == eq::MERGED_THROUGH_TRANS) {
          std::vector<std::shared_ptr<EqProof>> orderedChildren;
          bool nullCongruenceFound = false;
          for (const auto& child : eqpc->d_children)
          {
            if (child->d_id == eq::MERGED_THROUGH_CONGRUENCE
                && child->d_node.isNull())
            {
              nullCongruenceFound = true;
              Debug("pf::ee")
                  << "Have congruence with empty d_node. Splitting..."
                  << std::endl;
              orderedChildren.insert(orderedChildren.begin(),
                                     child->d_children[0]);
              orderedChildren.push_back(child->d_children[1]);
            }
            else
            {
              orderedChildren.push_back(child);
            }
          }

          if (nullCongruenceFound) {
            eqpc->d_children = orderedChildren;
            if (Debug.isOn("pf::ee"))
            {
              Debug("pf::ee")
                  << "Child proof's children have been reordered. It is now:"
                  << std::endl;
              eqpc->debug_print("pf::ee", 1);
            }
          }
        }

        eqp->d_children.push_back(eqpc);
      }
    }

    if (eqp) {
      if (eqp->d_children.size() == 0) {
        // Corner case where this is actually a disequality between two constants
        Debug("pf::ee") << "Encountered a constant disequality (not a transitivity proof): "
                        << eqp->d_node << std::endl;
        Assert(eqp->d_node[0][0].isConst());
        Assert(eqp->d_node[0][1].isConst());
        eqp->d_id = MERGED_THROUGH_CONSTANTS;
      } else if (eqp->d_children.size() == 1) {
        Node cnode = eqp->d_children[0]->d_node;
        Debug("pf::ee") << "Simplifying " << cnode << " from " << eqp->d_node
                        << std::endl;
        bool simpTrans = true;
        if (cnode.getKind() == kind::EQUAL)
        {
          // It may be the case that we have a proof of x = c2 and we want to
          // conclude x != c1. If this is the case, below we construct:
          //
          //          -------- MERGED_THROUGH_EQUALITY
          // x = c2   c1 != c2
          // ----------------- TRANS
          //     x != c1
          TNode c1 = t1.isConst() ? t1 : (t2.isConst() ? t2 : TNode::null());
          TNode nc = t1.isConst() ? t2 : (t2.isConst() ? t1 : TNode::null());
          Node c2;
          // merge constants transitivity
          for (unsigned i = 0; i < 2; i++)
          {
            if (cnode[i].isConst() && cnode[1 - i] == nc)
            {
              c2 = cnode[i];
              break;
            }
          }
          if (!c1.isNull() && !c2.isNull())
          {
            simpTrans = false;
            Assert(c1.getType().isComparableTo(c2.getType()));
            std::shared_ptr<EqProof> eqpmc = std::make_shared<EqProof>();
            eqpmc->d_id = MERGED_THROUGH_CONSTANTS;
            eqpmc->d_node = c1.eqNode(c2).eqNode(d_false);
            eqp->d_children.push_back(eqpmc);
          }
        }
        if (simpTrans)
        {
          // The transitivity proof has just one child. Simplify.
          std::shared_ptr<EqProof> temp = eqp->d_children[0];
          eqp->d_children.clear();
          *eqp = *temp;
        }
      }

      if (Debug.isOn("pf::ee"))
      {
        Debug("pf::ee") << "Disequality explanation final proof: " << std::endl;
        eqp->debug_print("pf::ee", 1);
      }
    }
  }
}

void EqualityEngine::explainPredicate(TNode p, bool polarity,
                                      std::vector<TNode>& assertions,
                                      EqProof* eqp) const {
  Debug("equality") << d_name << "::eq::explainPredicate(" << p << ")"
                    << std::endl;
  // Must have the term
  Assert(hasTerm(p));
  std::map<std::pair<EqualityNodeId, EqualityNodeId>, EqProof*> cache;
  if (Debug.isOn("equality::internal"))
  {
    debugPrintGraph();
  }
  // Get the explanation
  getExplanation(
      getNodeId(p), polarity ? d_trueId : d_falseId, assertions, cache, eqp);
}

void EqualityEngine::explainLit(TNode lit, std::vector<TNode>& assumptions)
{
  Assert(lit.getKind() != kind::AND);
  bool polarity = lit.getKind() != kind::NOT;
  TNode atom = polarity ? lit : lit[0];
  std::vector<TNode> tassumptions;
  if (atom.getKind() == kind::EQUAL)
  {
    Assert(hasTerm(atom[0]));
    Assert(hasTerm(atom[1]));
    if (!polarity)
    {
      // ensure that we are ready to explain the disequality
      AlwaysAssert(areDisequal(atom[0], atom[1], true));
    }
    else if (atom[0] == atom[1])
    {
      // no need to explain reflexivity
      return;
    }
    explainEquality(atom[0], atom[1], polarity, tassumptions);
  }
  else
  {
    explainPredicate(atom, polarity, tassumptions);
  }
  // ensure that duplicates are removed
  for (const TNode a : tassumptions)
  {
    if (std::find(assumptions.begin(), assumptions.end(), a)
        == assumptions.end())
    {
      Assert(!a.isNull());
      assumptions.push_back(a);
    }
  }
}

Node EqualityEngine::mkExplainLit(TNode lit)
{
  Assert(lit.getKind() != kind::AND);
  std::vector<TNode> assumptions;
  explainLit(lit, assumptions);
  Node ret;
  if (assumptions.empty())
  {
    ret = NodeManager::currentNM()->mkConst(true);
  }
  else if (assumptions.size() == 1)
  {
    ret = assumptions[0];
  }
  else
  {
    ret = NodeManager::currentNM()->mkNode(kind::AND, assumptions);
  }
  return ret;
}

void EqualityEngine::getExplanation(
    EqualityNodeId t1Id,
    EqualityNodeId t2Id,
    std::vector<TNode>& equalities,
    std::map<std::pair<EqualityNodeId, EqualityNodeId>, EqProof*>& cache,
    EqProof* eqp) const
{
  Trace("eq-exp") << d_name << "::eq::getExplanation({" << t1Id << "} "
                  << d_nodes[t1Id] << ", {" << t2Id << "} " << d_nodes[t2Id]
                  << ") size = " << cache.size() << std::endl;

  // determine if we have already computed the explanation.
  std::pair<EqualityNodeId, EqualityNodeId> cacheKey;
  std::map<std::pair<EqualityNodeId, EqualityNodeId>, EqProof*>::iterator it;
  if (!eqp)
  {
    // If proofs are disabled, we order the ids, since explaining t1 = t2 is the
    // same as explaining t2 = t1.
    cacheKey = std::minmax(t1Id, t2Id);
    it = cache.find(cacheKey);
    if (it != cache.end())
    {
      return;
    }
  }
  else
  {
    // If proofs are enabled, note that proofs are sensitive to the order of t1
    // and t2, so we don't sort the ids in this case. TODO: Depending on how
    // issue #2965 is resolved, we may be able to revisit this, if it is the
    // case that proof/uf_proof.h,cpp is robust to equality ordering.
    cacheKey = std::pair<EqualityNodeId, EqualityNodeId>(t1Id, t2Id);
    it = cache.find(cacheKey);
    if (it != cache.end())
    {
      if (it->second)
      {
        eqp->d_id = it->second->d_id;
        eqp->d_children.insert(eqp->d_children.end(),
                               it->second->d_children.begin(),
                               it->second->d_children.end());
        eqp->d_node = it->second->d_node;
      }
      else
      {
        // We may have cached null in its place, create the trivial proof now.
        Assert(d_nodes[t1Id] == d_nodes[t2Id]);
        Assert(eqp->d_id == MERGED_THROUGH_REFLEXIVITY);
        eqp->d_node = d_nodes[t1Id].eqNode(d_nodes[t1Id]);
      }
      return;
    }
  }
  cache[cacheKey] = eqp;

  // We can only explain the nodes that got merged
#ifdef CVC4_ASSERTIONS
  bool canExplain = getEqualityNode(t1Id).getFind() == getEqualityNode(t2Id).getFind()
                  || (d_done && isConstant(t1Id) && isConstant(t2Id));

  if (!canExplain) {
    Warning() << "Can't explain equality:" << std::endl;
    Warning() << d_nodes[t1Id] << " with find " << d_nodes[getEqualityNode(t1Id).getFind()] << std::endl;
    Warning() << d_nodes[t2Id] << " with find " << d_nodes[getEqualityNode(t2Id).getFind()] << std::endl;
  }
  Assert(canExplain);
#endif

  // If the nodes are the same, we're done
  if (t1Id == t2Id){
    if( eqp ) {
      if (options::proofNew())
      {
        // ignore equalities between function symbols, i.e. internal nullary
        // non-constant nodes.
        //
        // Note that this is robust for HOL because in that case function
        // symbols are not internal nodes
        if (d_isInternal[t1Id] && d_nodes[t1Id].getNumChildren() == 0
            && !d_isConstant[t1Id])
        {
          eqp->d_node = Node::null();
        }
        else
        {
          Assert(d_nodes[t1Id].getKind() != kind::BUILTIN);
          eqp->d_node = d_nodes[t1Id].eqNode(d_nodes[t1Id]);
        }
      }
      else if ((d_nodes[t1Id].getKind() == kind::BUILTIN)
               && (d_nodes[t1Id].getConst<Kind>() == kind::SELECT))
      {
        std::vector<Node> no_children;
        eqp->d_node = NodeManager::currentNM()->mkNode(kind::PARTIAL_SELECT_0, no_children);
      }
      else
      {
        eqp->d_node = ProofManager::currentPM()->mkOp(d_nodes[t1Id]);
      }
    }
    return;
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
    EqualityNodeId currentNode = current.d_nodeId;

    Debug("equality") << d_name << "::eq::getExplanation(): currentNode = {"
                      << currentNode << "} " << d_nodes[currentNode]
                      << std::endl;

    // Go through the equality edges of this node
    EqualityEdgeId currentEdge = d_equalityGraph[currentNode];
    if (Debug.isOn("equality")) {
      Debug("equality") << d_name << "::eq::getExplanation(): edgesId =  " << currentEdge << std::endl;
      Debug("equality") << d_name << "::eq::getExplanation(): edges =  " << edgesToString(currentEdge) << std::endl;
    }

    while (currentEdge != null_edge) {
      // Get the edge
      const EqualityEdge& edge = d_equalityEdges[currentEdge];

      // If not just the backwards edge
      if ((currentEdge | 1u) != (current.d_edgeId | 1u))
      {
        Debug("equality") << d_name
                          << "::eq::getExplanation(): currentEdge = ({"
                          << currentNode << "} " << d_nodes[currentNode]
                          << ", {" << edge.getNodeId() << "} "
                          << d_nodes[edge.getNodeId()] << ")" << std::endl;

        // Did we find the path
        if (edge.getNodeId() == t2Id) {

          Debug("equality") << d_name << "::eq::getExplanation(): path found: " << std::endl;

          std::vector<std::shared_ptr<EqProof>> eqp_trans;

          // Reconstruct the path
          do {
            // The current node
            currentNode = bfsQueue[currentIndex].d_nodeId;
            EqualityNodeId edgeNode = d_equalityEdges[currentEdge].getNodeId();
            unsigned reasonType = d_equalityEdges[currentEdge].getReasonType();
            Node reason = d_equalityEdges[currentEdge].getReason();

            Debug("equality")
                << d_name
                << "::eq::getExplanation(): currentEdge = " << currentEdge
                << ", currentNode = " << currentNode << std::endl;
            Debug("equality")
                << d_name << "                       targetNode = {" << edgeNode
                << "} " << d_nodes[edgeNode] << std::endl;
            Debug("equality")
                << d_name << "                       in currentEdge = ({"
                << currentNode << "} " << d_nodes[currentNode] << ", {"
                << edge.getNodeId() << "} " << d_nodes[edge.getNodeId()] << ")"
                << std::endl;
            Debug("equality")
                << d_name << "                       reason type = "
                << static_cast<MergeReasonType>(reasonType) << std::endl;

            std::shared_ptr<EqProof> eqpc;;
            // Make child proof if a proof is being constructed
            if (eqp) {
              eqpc = std::make_shared<EqProof>();
              eqpc->d_id = reasonType;
            }

            // Add the actual equality to the vector
            switch (reasonType) {
            case MERGED_THROUGH_CONGRUENCE: {
              // f(x1, x2) == f(y1, y2) because x1 = y1 and x2 = y2
              Debug("equality")
                  << d_name
                  << "::eq::getExplanation(): due to congruence, going deeper"
                  << std::endl;
              const FunctionApplication& f1 =
                  d_applications[currentNode].d_original;
              const FunctionApplication& f2 =
                  d_applications[edgeNode].d_original;

              Debug("equality") << push;
              Debug("equality") << "Explaining left hand side equalities" << std::endl;
              std::shared_ptr<EqProof> eqpc1 =
                  eqpc ? std::make_shared<EqProof>() : nullptr;
              getExplanation(f1.d_a, f2.d_a, equalities, cache, eqpc1.get());
              Debug("equality") << "Explaining right hand side equalities" << std::endl;
              std::shared_ptr<EqProof> eqpc2 =
                  eqpc ? std::make_shared<EqProof>() : nullptr;
              getExplanation(f1.d_b, f2.d_b, equalities, cache, eqpc2.get());
              if (eqpc)
              {
                eqpc->d_children.push_back(eqpc1);
                eqpc->d_children.push_back(eqpc2);
                if (options::proofNew())
                {
                  // build conclusion if ids correspond to non-internal nodes or
                  // if non-internal nodes can be retrieved from them (in the
                  // case of n-ary applications), otherwise leave conclusion as
                  // null. This is only done for congruence kinds, since
                  // congruence is not used otherwise.
                  Kind k = d_nodes[currentNode].getKind();
                  if (d_congruenceKinds[k])
                  {
                    buildEqConclusion(currentNode, edgeNode, eqpc.get());
                  }
                  else
                  {
                    Assert(k == kind::EQUAL)
                        << "not an internal node " << d_nodes[currentNode]
                        << " with non-congruence with " << k << "\n";
                  }
                }
                else if (d_nodes[currentNode].getKind() == kind::EQUAL)
                {
                  //leave node null for now
                  eqpc->d_node = Node::null();
                }
                else
                {
                  if (d_nodes[f1.d_a].getKind() == kind::APPLY_UF
                      || d_nodes[f1.d_a].getKind() == kind::SELECT
                      || d_nodes[f1.d_a].getKind() == kind::STORE)
                  {
                    eqpc->d_node = d_nodes[f1.d_a];
                  }
                  else
                  {
                    if (d_nodes[f1.d_a].getKind() == kind::BUILTIN
                        && d_nodes[f1.d_a].getConst<Kind>() == kind::SELECT)
                    {
                      eqpc->d_node = NodeManager::currentNM()->mkNode(
                          kind::PARTIAL_SELECT_1, d_nodes[f1.d_b]);
                      // The first child is a PARTIAL_SELECT_0.
                      // Give it a child so that we know what kind of (read) it is, when we dump to LFSC.
                      Assert(eqpc->d_children[0]->d_node.getKind()
                             == kind::PARTIAL_SELECT_0);
                      Assert(eqpc->d_children[0]->d_children.size() == 0);

                      eqpc->d_children[0]->d_node =
                          NodeManager::currentNM()->mkNode(
                              kind::PARTIAL_SELECT_0, d_nodes[f1.d_b]);
                    }
                    else
                    {
                      eqpc->d_node = NodeManager::currentNM()->mkNode(
                          kind::PARTIAL_APPLY_UF,
                          ProofManager::currentPM()->mkOp(d_nodes[f1.d_a]),
                          d_nodes[f1.d_b]);
                    }
                  }
                }
              }
              Debug("equality") << pop;
              break;
            }

            case MERGED_THROUGH_REFLEXIVITY: {
              // x1 == x1
              Debug("equality") << d_name << "::eq::getExplanation(): due to reflexivity, going deeper" << std::endl;
              EqualityNodeId eqId = currentNode == d_trueId ? edgeNode : currentNode;
              const FunctionApplication& eq = d_applications[eqId].d_original;
              Assert(eq.isEquality()) << "Must be an equality";

              // Explain why a = b constant
              Debug("equality") << push;
              std::shared_ptr<EqProof> eqpc1 =
                  eqpc ? std::make_shared<EqProof>() : nullptr;
              getExplanation(eq.d_a, eq.d_b, equalities, cache, eqpc1.get());
              if( eqpc ){
                eqpc->d_children.push_back( eqpc1 );
              }
              Debug("equality") << pop;

              break;
            }

            case MERGED_THROUGH_CONSTANTS: {
              // f(c1, ..., cn) = c semantically, we can just ignore it
              Debug("equality") << d_name << "::eq::getExplanation(): due to constants, explain the constants" << std::endl;
              Debug("equality") << push;

              // Get the node we interpreted
              TNode interpreted;
              if (eqpc && options::proofNew())
              {
                // build the conclusion f(c1, ..., cn) = c
                if (d_nodes[currentNode].isConst())
                {
                  interpreted = d_nodes[edgeNode];
                  eqpc->d_node = d_nodes[edgeNode].eqNode(d_nodes[currentNode]);
                }
                else
                {
                  interpreted = d_nodes[currentNode];
                  eqpc->d_node = d_nodes[currentNode].eqNode(d_nodes[edgeNode]);
                }
              }
              else
              {
                interpreted = d_nodes[currentNode].isConst()
                                  ? d_nodes[edgeNode]
                                  : d_nodes[currentNode];
              }

              // Explain why a is a constant by explaining each argument
              for (unsigned i = 0; i < interpreted.getNumChildren(); ++ i) {
                EqualityNodeId childId = getNodeId(interpreted[i]);
                Assert(isConstant(childId));
                std::shared_ptr<EqProof> eqpcc =
                    eqpc ? std::make_shared<EqProof>() : nullptr;
                getExplanation(childId,
                               getEqualityNode(childId).getFind(),
                               equalities,
                               cache,
                               eqpcc.get());
                if( eqpc ) {
                  eqpc->d_children.push_back( eqpcc );
                  if (Debug.isOn("pf::ee"))
                  {
                    Debug("pf::ee")
                        << "MERGED_THROUGH_CONSTANTS. Dumping the child proof"
                        << std::endl;
                    eqpc->debug_print("pf::ee", 1);
                  }
                }
              }

              Debug("equality") << pop;
              break;
            }

            default: {
              // Construct the equality
              Debug("equality") << d_name << "::eq::getExplanation(): adding: "
                                << reason << std::endl;
              Debug("equality")
                  << d_name << "::eq::getExplanation(): reason type = "
                  << static_cast<MergeReasonType>(reasonType) << std::endl;
              Node a = d_nodes[currentNode];
              Node b = d_nodes[d_equalityEdges[currentEdge].getNodeId()];

              if (eqpc) {
                //apply proof reconstruction processing (when eqpc is non-null)
                if (d_pathReconstructionTriggers.find(reasonType) != d_pathReconstructionTriggers.end()) {
                  d_pathReconstructionTriggers.find(reasonType)
                      ->second->notify(reasonType, reason, a, b, equalities,
                                       eqpc.get());
                }
                if (reasonType == MERGED_THROUGH_EQUALITY) {
                  // in the new proof infrastructure we can assume that "theory
                  // assumptions", which are a consequence of theory reasoning
                  // on other assumptions, are externally justified. In this
                  // case we can use (= a b) directly as the conclusion here.
                  eqpc->d_node = !options::proofNew() ? reason : b.eqNode(a);
                } else {
                  // The LFSC translator prefers (not (= a b)) over (= (= a b) false)

                  if (a == NodeManager::currentNM()->mkConst(false)) {
                    eqpc->d_node = b.notNode();
                  } else if (b == NodeManager::currentNM()->mkConst(false)) {
                    eqpc->d_node = a.notNode();
                  } else {
                    eqpc->d_node = b.eqNode(a);
                  }
                }
                eqpc->d_id = reasonType;
              }
              equalities.push_back(reason);
              break;
            }
            }

            // Go to the previous
            currentEdge = bfsQueue[currentIndex].d_edgeId;
            currentIndex = bfsQueue[currentIndex].d_previousIndex;

            //---from Morgan---
            if (eqpc != NULL && eqpc->d_id == MERGED_THROUGH_REFLEXIVITY) {
              if(eqpc->d_node.isNull()) {
                Assert(eqpc->d_children.size() == 1);
                std::shared_ptr<EqProof> p = eqpc;
                eqpc = p->d_children[0];
              } else {
                Assert(eqpc->d_children.empty());
              }
            }
            //---end from Morgan---

            eqp_trans.push_back(eqpc);
          } while (currentEdge != null_id);

          if (eqp) {
            if(eqp_trans.size() == 1) {
              *eqp = *eqp_trans[0];
            } else {
              eqp->d_id = MERGED_THROUGH_TRANS;
              eqp->d_children.insert( eqp->d_children.end(), eqp_trans.begin(), eqp_trans.end() );
              if (options::proofNew())
              {
                // build conclusion in case of equality between non-internal
                // nodes or of n-ary congruence kinds, otherwise leave as
                // null. The latter is necessary for the overall handling of
                // congruence proofs involving n-ary kinds, see
                // EqProof::reduceNestedCongruence for more details.
                buildEqConclusion(t1Id, t2Id, eqp);
              }
              else
              {
                eqp->d_node = NodeManager::currentNM()->mkNode(
                    kind::EQUAL, d_nodes[t1Id], d_nodes[t2Id]);
              }
            }
            if (Debug.isOn("pf::ee"))
            {
              eqp->debug_print("pf::ee", 1);
            }
          }

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
  addTermInternal(eq[0]);
  addTermInternal(eq[1]);

  bool skipTrigger = false;

  // If they are equal or disequal already, no need for the trigger
  if (areEqual(eq[0], eq[1])) {
    d_notify.eqNotifyTriggerPredicate(eq, true);
    skipTrigger = true;
  }
  if (areDisequal(eq[0], eq[1], true)) {
    d_notify.eqNotifyTriggerPredicate(eq, false);
    skipTrigger = true;
  }

  if (skipTrigger) {
    return;
  }

  // Add the equality
  addTermInternal(eq);

  // Positive trigger
  addTriggerEqualityInternal(eq[0], eq[1], eq, true);
  // Negative trigger
  addTriggerEqualityInternal(eq, d_false, eq, false);
}

void EqualityEngine::addTriggerPredicate(TNode predicate) {
  Assert(predicate.getKind() != kind::NOT);
  if (predicate.getKind() == kind::EQUAL)
  {
    // equality is handled separately
    return addTriggerEquality(predicate);
  }
  Assert(d_congruenceKinds.tst(predicate.getKind()))
      << "No point in adding non-congruence predicates";

  if (d_done) {
    return;
  }

  // Add the term
  addTermInternal(predicate);

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

  Debug("equality") << d_name << "::eq::addTrigger(" << t1 << ", " << t2 << ", " << trigger << ")" << std::endl;

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

  Debug("equality") << d_name << "::eq::addTrigger(" << trigger << "): " << t1Id << " (" << t1classId << ") = " << t2Id << " (" << t2classId << ")" << std::endl;

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

  Debug("equality") << d_name << "::eq::addTrigger(" << t1 << "," << t2 << ") => (" << t1NewTriggerId << ", " << t2NewTriggerId << ")" << std::endl;
}

Node EqualityEngine::evaluateTerm(TNode node) {
  Debug("equality::evaluation") << d_name << "::eq::evaluateTerm(" << node << ")" << std::endl;
  NodeBuilder<> builder;
  builder << node.getKind();
  if (node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    builder << node.getOperator();
  }
  for (unsigned i = 0; i < node.getNumChildren(); ++ i) {
    TNode child = node[i];
    TNode childRep = getRepresentative(child);
    Debug("equality::evaluation") << d_name << "::eq::evaluateTerm: " << child << " -> " << childRep << std::endl;
    Assert(childRep.isConst());
    builder << childRep;
  }
  Node newNode = builder;
  return Rewriter::rewrite(newNode);
}

void EqualityEngine::processEvaluationQueue() {

  Debug("equality::evaluation") << d_name << "::eq::processEvaluationQueue(): start" << std::endl;

  while (!d_evaluationQueue.empty()) {
    // Get the node
    EqualityNodeId id = d_evaluationQueue.front();
    d_evaluationQueue.pop();

    // Replace the children with their representatives (must be constants)
    Node nodeEvaluated = evaluateTerm(d_nodes[id]);
    Debug("equality::evaluation") << d_name << "::eq::processEvaluationQueue(): " << d_nodes[id] << " evaluates to " << nodeEvaluated << std::endl;
    Assert(nodeEvaluated.isConst());
    addTermInternal(nodeEvaluated);
    EqualityNodeId nodeEvaluatedId = getNodeId(nodeEvaluated);

    // Enqueue the semantic equality
    enqueue(MergeCandidate(id, nodeEvaluatedId, MERGED_THROUGH_CONSTANTS, TNode::null()));
  }

  Debug("equality::evaluation") << d_name << "::eq::processEvaluationQueue(): done" << std::endl;
}

void EqualityEngine::propagate() {

  if (d_inPropagate) {
    // We're already in propagate, go back
    return;
  }

  // Make sure we don't get in again
  ScopedBool inPropagate(d_inPropagate, true);

  Debug("equality") << d_name << "::eq::propagate()" << std::endl;

  while (!d_propagationQueue.empty() || !d_evaluationQueue.empty()) {

    if (d_done) {
      // If we're done, just empty the queue
      while (!d_propagationQueue.empty()) d_propagationQueue.pop_front();
      while (!d_evaluationQueue.empty()) d_evaluationQueue.pop();
      continue;
    }

    // Process any evaluation requests
    if (!d_evaluationQueue.empty()) {
      processEvaluationQueue();
      continue;
    }

    // The current merge candidate
    const MergeCandidate current = d_propagationQueue.front();
    d_propagationQueue.pop_front();

    // Get the representatives
    EqualityNodeId t1classId = getEqualityNode(current.d_t1Id).getFind();
    EqualityNodeId t2classId = getEqualityNode(current.d_t2Id).getFind();

    // If already the same, we're done
    if (t1classId == t2classId) {
      continue;
    }

    Debug("equality::internal") << d_name << "::eq::propagate(): t1: " << (d_isInternal[t1classId] ? "internal" : "proper") << std::endl;
    Debug("equality::internal") << d_name << "::eq::propagate(): t2: " << (d_isInternal[t2classId] ? "internal" : "proper") << std::endl;

    // Get the nodes of the representatives
    EqualityNode& node1 = getEqualityNode(t1classId);
    EqualityNode& node2 = getEqualityNode(t2classId);

    Assert(node1.getFind() == t1classId);
    Assert(node2.getFind() == t2classId);

    // Add the actual equality to the equality graph
    addGraphEdge(
        current.d_t1Id, current.d_t2Id, current.d_type, current.d_reason);

    // If constants are being merged we're done
    if (d_isConstant[t1classId] && d_isConstant[t2classId]) {
      // When merging constants we are inconsistent, hence done
      d_done = true;
      // But in order to keep invariants (edges = 2*equalities) we put an equalities in
      // Note that we can explain this merge as we have a graph edge
      d_assertedEqualities.push_back(Equality(null_id, null_id));
      d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;
      // Notify
      if (d_performNotify) {
        d_notify.eqNotifyConstantTermMerge(d_nodes[t1classId], d_nodes[t2classId]);
      }
      // Empty the queue and exit
      continue;
    }

    // Vector to collect the triggered events
    std::vector<TriggerId> triggers;

    // Figure out the merge preference
    EqualityNodeId mergeInto = t1classId;
    if (d_isInternal[t2classId] != d_isInternal[t1classId]) {
      // We always keep non-internal nodes as representatives: if any node in
      // the class is non-internal, then the representative will be non-internal
      if (d_isInternal[t1classId]) {
        mergeInto = t2classId;
      } else {
        mergeInto = t1classId;
      }
    } else if (d_isConstant[t2classId] != d_isConstant[t1classId]) {
      // We always keep constants as representatives: if any (at most one) node
      // in the class in a constant, then the representative will be a constant
      if (d_isConstant[t2classId]) {
        mergeInto = t2classId;
      } else {
        mergeInto = t1classId;
      }
    } else if (node2.getSize() > node1.getSize()) {
      // We always merge into the bigger class to reduce the amount of traversing
      // we need to do
      mergeInto = t2classId;
    }

    if (mergeInto == t2classId) {
      Debug("equality") << d_name << "::eq::propagate(): merging "
                        << d_nodes[current.d_t1Id] << " into "
                        << d_nodes[current.d_t2Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t2classId, t1classId));
      d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;
      if (!merge(node2, node1, triggers)) {
        d_done = true;
      }
    } else {
      Debug("equality") << d_name << "::eq::propagate(): merging "
                        << d_nodes[current.d_t2Id] << " into "
                        << d_nodes[current.d_t1Id] << std::endl;
      d_assertedEqualities.push_back(Equality(t1classId, t2classId));
      d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;
    if (!merge(node1, node2, triggers)) {
        d_done = true;
      }
    }

    // If not merging internal nodes, notify the master
    if (d_masterEqualityEngine && !d_isInternal[t1classId] && !d_isInternal[t2classId]) {
      d_masterEqualityEngine->assertEqualityInternal(d_nodes[t1classId], d_nodes[t2classId], TNode::null());
      d_masterEqualityEngine->propagate();
    }

    // Notify the triggers
    if (d_performNotify && !d_done) {
      for (size_t trigger_i = 0, trigger_end = triggers.size(); trigger_i < trigger_end && !d_done; ++ trigger_i) {
        const TriggerInfo& triggerInfo = d_equalityTriggersOriginal[triggers[trigger_i]];
        if (triggerInfo.d_trigger.getKind() == kind::EQUAL)
        {
          // Special treatment for disequalities
          if (!triggerInfo.d_polarity)
          {
            // Store that we are propagating a diseauality
            TNode equality = triggerInfo.d_trigger;
            EqualityNodeId original = getNodeId(equality);
            TNode lhs = equality[0];
            TNode rhs = equality[1];
            EqualityNodeId lhsId = getNodeId(lhs);
            EqualityNodeId rhsId = getNodeId(rhs);
            // We use the THEORY_LAST as a marker for "marked as propagated, reasons stored".
            // This tag is added to an internal theories set that is only inserted in, so this is
            // safe. Had we iterated over, or done other set operations this might be dangerous.
            if (!hasPropagatedDisequality(THEORY_LAST, lhsId, rhsId)) {
              if (!hasPropagatedDisequality(lhsId, rhsId)) {
                d_deducedDisequalityReasons.push_back(EqualityPair(original, d_falseId));
              }
              storePropagatedDisequality(THEORY_LAST, lhsId, rhsId);
              if (!d_notify.eqNotifyTriggerPredicate(triggerInfo.d_trigger,
                                                     triggerInfo.d_polarity))
              {
                d_done = true;
              }
            }
          }
          else
          {
            // Equalities are simple
            if (!d_notify.eqNotifyTriggerPredicate(triggerInfo.d_trigger,
                                                   triggerInfo.d_polarity))
            {
              d_done = true;
            }
          }
        }
        else
        {
          if (!d_notify.eqNotifyTriggerPredicate(triggerInfo.d_trigger,
                                                 triggerInfo.d_polarity))
          {
            d_done = true;
          }
        }
      }
    }
  }
}

void EqualityEngine::debugPrintGraph() const {
  Debug("equality::graph") << std::endl << "Dumping graph" << std::endl;
  for (EqualityNodeId nodeId = 0; nodeId < d_nodes.size(); ++ nodeId) {

    Debug("equality::graph") << d_nodes[nodeId] << " " << nodeId << "(" << getEqualityNode(nodeId).getFind() << "):";

    EqualityEdgeId edgeId = d_equalityGraph[nodeId];
    while (edgeId != null_edge) {
      const EqualityEdge& edge = d_equalityEdges[edgeId];
      Debug("equality::graph") << " [" << edge.getNodeId() << "] " << d_nodes[edge.getNodeId()] << ":" << edge.getReason();
      edgeId = edge.getNext();
    }

    Debug("equality::graph") << std::endl;
  }
  Debug("equality::graph") << std::endl;
}

bool EqualityEngine::areEqual(TNode t1, TNode t2) const {
  Debug("equality") << d_name << "::eq::areEqual(" << t1 << "," << t2 << ")";

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  bool result = getEqualityNode(t1).getFind() == getEqualityNode(t2).getFind();
  Debug("equality") << (result ? "\t(YES)" : "\t(NO)") << std::endl;
  return result;
}

bool EqualityEngine::areDisequal(TNode t1, TNode t2, bool ensureProof) const
{
  Debug("equality") << d_name << "::eq::areDisequal(" << t1 << "," << t2 << ")";

  // Add the terms
  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Get ids
  EqualityNodeId t1Id = getNodeId(t1);
  EqualityNodeId t2Id = getNodeId(t2);

  // If we propagated this disequality we're true
  if (hasPropagatedDisequality(t1Id, t2Id)) {
    Debug("equality") << "\t(YES)" << std::endl;
    return true;
  }

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
      nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
    }
    Debug("equality") << "\t(YES)" << std::endl;
    return true;
  }

  // Create the equality
  FunctionApplication eqNormalized(APP_EQUALITY, t1ClassId, t2ClassId);
  ApplicationIdsMap::const_iterator find = d_applicationLookup.find(eqNormalized);
  if (find != d_applicationLookup.end()) {
    if (getEqualityNode(find->second).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        const FunctionApplication original =
            d_applications[find->second].d_original;
        nonConst->d_deducedDisequalityReasons.push_back(
            EqualityPair(t1Id, original.d_a));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(find->second, d_falseId));
        nonConst->d_deducedDisequalityReasons.push_back(
            EqualityPair(t2Id, original.d_b));
        nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
      }
      Debug("equality") << "\t(YES)" << std::endl;
      return true;
    }
  }

  // Check the symmetric disequality
  std::swap(eqNormalized.d_a, eqNormalized.d_b);
  find = d_applicationLookup.find(eqNormalized);
  if (find != d_applicationLookup.end()) {
    if (getEqualityNode(find->second).getFind() == getEqualityNode(d_falseId).getFind()) {
      if (ensureProof) {
        const FunctionApplication original =
            d_applications[find->second].d_original;
        nonConst->d_deducedDisequalityReasons.push_back(
            EqualityPair(t2Id, original.d_a));
        nonConst->d_deducedDisequalityReasons.push_back(EqualityPair(find->second, d_falseId));
        nonConst->d_deducedDisequalityReasons.push_back(
            EqualityPair(t1Id, original.d_b));
        nonConst->storePropagatedDisequality(THEORY_LAST, t1Id, t2Id);
      }
      Debug("equality") << "\t(YES)" << std::endl;
      return true;
    }
  }

  // Couldn't deduce dis-equalityReturn whether the terms are disequal
  Debug("equality") << "\t(NO)" << std::endl;
  return false;
}

size_t EqualityEngine::getSize(TNode t) {
  // Add the term
  addTermInternal(t);
  return getEqualityNode(getEqualityNode(t).getFind()).getSize();
}


void EqualityEngine::addPathReconstructionTrigger(unsigned trigger, const PathReconstructionNotify* notify) {
  // Currently we can only inform one callback per trigger
  Assert(d_pathReconstructionTriggers.find(trigger)
         == d_pathReconstructionTriggers.end());
  d_pathReconstructionTriggers[trigger] = notify;
}

unsigned EqualityEngine::getFreshMergeReasonType() {
  return d_freshMergeReasonType++;
}

std::string EqualityEngine::identify() const { return d_name; }

void EqualityEngine::addTriggerTerm(TNode t, TheoryId tag)
{
  Debug("equality::trigger") << d_name << "::eq::addTriggerTerm(" << t << ", " << tag << ")" << std::endl;

  Assert(tag != THEORY_LAST);

  if (d_done) {
    return;
  }

  // Add the term if it's not already there
  addTermInternal(t);

  if (!d_anyTermsAreTriggers)
  {
    // if we are not using triggers, we only add the term, but not as a trigger
    return;
  }

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
      Debug("equality::trigger") << d_name << "::eq::addTriggerTerm(" << t << ", " << tag << "): already have this trigger in class with " << d_nodes[triggerId] << std::endl;
      if (eqNodeId != triggerId && !d_notify.eqNotifyTriggerTermEquality(tag, t, d_nodes[triggerId], true)) {
        d_done = true;
      }
    }
  } else {

    // Check for disequalities by going through the equivalence class looking for equalities in the
    // uselists that have been asserted to false. All the representatives appearing on the other
    // side of such disequalities, that have the tag on, are put in a set.
    TaggedEqualitiesSet disequalitiesToNotify;
    TheoryIdSet tags = TheoryIdSetUtil::setInsert(tag);
    getDisequalities(!d_isConstant[classId], classId, tags, disequalitiesToNotify);

    // Trigger data
    TheoryIdSet newSetTags;
    EqualityNodeId newSetTriggers[THEORY_LAST];
    unsigned newSetTriggersSize;

    // Setup the data for the new set
    if (triggerSetRef != null_set_id) {
      // Get the existing set
      TriggerTermSet& triggerSet = getTriggerTermSet(triggerSetRef);
      // Initialize the new set for copy/insert
      newSetTags = TheoryIdSetUtil::setInsert(tag, triggerSet.d_tags);
      newSetTriggersSize = 0;
      // Copy into to new one, and insert the new tag/id
      unsigned i = 0;
      TheoryIdSet tags2 = newSetTags;
      TheoryId current;
      while ((current = TheoryIdSetUtil::setPop(tags2)) != THEORY_LAST)
      {
        // Remove from the tags
        tags2 = TheoryIdSetUtil::setRemove(current, tags2);
        // Insert the id into the triggers
        newSetTriggers[newSetTriggersSize++] =
            current == tag ? eqNodeId : triggerSet.d_triggers[i++];
      }
    } else {
      // Setup a singleton
      newSetTags = TheoryIdSetUtil::setInsert(tag);
      newSetTriggers[0] = eqNodeId;
      newSetTriggersSize = 1;
    }

    // Add it to the list for backtracking
    d_triggerTermSetUpdates.push_back(TriggerSetUpdate(classId, triggerSetRef));
    d_triggerTermSetUpdatesSize = d_triggerTermSetUpdatesSize + 1;
    // Mark the the new set as a trigger
    d_nodeIndividualTrigger[classId] = triggerSetRef = newTriggerTermSet(newSetTags, newSetTriggers, newSetTriggersSize);

    // Propagate trigger term disequalities we remembered
    Debug("equality::trigger") << d_name << "::eq::addTriggerTerm(" << t << ", " << tag << "): propagating " << disequalitiesToNotify.size() << " disequalities " << std::endl;
    propagateTriggerTermDisequalities(tags, triggerSetRef, disequalitiesToNotify);
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
  TheoryIdSet tags = triggerSet.d_tags;
  while (TheoryIdSetUtil::setPop(tags) != tag)
  {
    ++ i;
  }
  return d_nodes[triggerSet.d_triggers[i]];
}

void EqualityEngine::storeApplicationLookup(FunctionApplication& funNormalized, EqualityNodeId funId) {
  Assert(d_applicationLookup.find(funNormalized) == d_applicationLookup.end());
  d_applicationLookup[funNormalized] = funId;
  d_applicationLookups.push_back(funNormalized);
  d_applicationLookupsCount = d_applicationLookupsCount + 1;
  Debug("equality::backtrack") << "d_applicationLookupsCount = " << d_applicationLookupsCount << std::endl;
  Debug("equality::backtrack") << "d_applicationLookups.size() = " << d_applicationLookups.size() << std::endl;
  Assert(d_applicationLookupsCount == d_applicationLookups.size());

  // If an equality over constants we merge to false
  if (funNormalized.isEquality()) {
    if (funNormalized.d_a == funNormalized.d_b)
    {
      enqueue(MergeCandidate(funId, d_trueId, MERGED_THROUGH_REFLEXIVITY, TNode::null()));
    }
    else if (d_isConstant[funNormalized.d_a] && d_isConstant[funNormalized.d_b])
    {
      enqueue(MergeCandidate(funId, d_falseId, MERGED_THROUGH_CONSTANTS, TNode::null()));
    }
  }
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
      UseListNodeId currentUseId = currentNode.getUseList();
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

EqualityEngine::TriggerTermSetRef EqualityEngine::newTriggerTermSet(
    TheoryIdSet newSetTags,
    EqualityNodeId* newSetTriggers,
    unsigned newSetTriggersSize)
{
  // Size of the required set
  size_t size = sizeof(TriggerTermSet) + newSetTriggersSize*sizeof(EqualityNodeId);
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
  newSet.d_tags = newSetTags;
  for (unsigned i = 0; i < newSetTriggersSize; ++i) {
    newSet.d_triggers[i] = newSetTriggers[i];
  }
  // Return the new reference
  return newTriggerSetRef;
}

bool EqualityEngine::hasPropagatedDisequality(EqualityNodeId lhsId, EqualityNodeId rhsId) const {
  EqualityPair eq(lhsId, rhsId);
  bool propagated = d_propagatedDisequalities.find(eq) != d_propagatedDisequalities.end();
#ifdef CVC4_ASSERTIONS
  bool stored = d_disequalityReasonsMap.find(eq) != d_disequalityReasonsMap.end();
  Assert(propagated == stored) << "These two should be in sync";
#endif
  Debug("equality::disequality") << d_name << "::eq::hasPropagatedDisequality(" << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ") => " << (propagated ? "true" : "false") << std::endl;
  return propagated;
}

bool EqualityEngine::hasPropagatedDisequality(TheoryId tag, EqualityNodeId lhsId, EqualityNodeId rhsId) const {

  EqualityPair eq(lhsId, rhsId);

  PropagatedDisequalitiesMap::const_iterator it = d_propagatedDisequalities.find(eq);
  if (it == d_propagatedDisequalities.end()) {
    Assert(d_disequalityReasonsMap.find(eq) == d_disequalityReasonsMap.end())
        << "Why do we have a proof if not propagated";
    Debug("equality::disequality") << d_name << "::eq::hasPropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ") => false" << std::endl;
    return false;
  }
  Assert(d_disequalityReasonsMap.find(eq) != d_disequalityReasonsMap.end())
      << "We propagated but there is no proof";
  bool result = TheoryIdSetUtil::setContains(tag, (*it).second);
  Debug("equality::disequality") << d_name << "::eq::hasPropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ") => " << (result ? "true" : "false") << std::endl;
  return result;
}


void EqualityEngine::storePropagatedDisequality(TheoryId tag, EqualityNodeId lhsId, EqualityNodeId rhsId) {
  Assert(!hasPropagatedDisequality(tag, lhsId, rhsId))
      << "Check before you store it";
  Assert(lhsId != rhsId) << "Wow, wtf!";

  Debug("equality::disequality") << d_name << "::eq::storePropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << ")" << std::endl;

  EqualityPair pair1(lhsId, rhsId);
  EqualityPair pair2(rhsId, lhsId);

  // Store the fact that we've propagated this already
  TheoryIdSet notified = 0;
  PropagatedDisequalitiesMap::const_iterator find = d_propagatedDisequalities.find(pair1);
  if (find == d_propagatedDisequalities.end()) {
    notified = TheoryIdSetUtil::setInsert(tag);
  } else {
    notified = TheoryIdSetUtil::setInsert(tag, (*find).second);
  }
  d_propagatedDisequalities[pair1] = notified;
  d_propagatedDisequalities[pair2] = notified;

  // Store the proof if provided
  if (d_deducedDisequalityReasons.size() > d_deducedDisequalityReasonsSize) {
    Debug("equality::disequality") << d_name << "::eq::storePropagatedDisequality(" << tag << ", " << d_nodes[lhsId] << ", " << d_nodes[rhsId] << "): storing proof" << std::endl;
    Assert(d_disequalityReasonsMap.find(pair1) == d_disequalityReasonsMap.end())
        << "There can't be a proof if you're adding a new one";
    DisequalityReasonRef ref(d_deducedDisequalityReasonsSize, d_deducedDisequalityReasons.size());
#ifdef CVC4_ASSERTIONS
    // Check that the reasons are valid
    for (unsigned i = ref.d_mergesStart; i < ref.d_mergesEnd; ++i)
    {
      Assert(
          getEqualityNode(d_deducedDisequalityReasons[i].first).getFind()
          == getEqualityNode(d_deducedDisequalityReasons[i].second).getFind());
    }
#endif
    if (Debug.isOn("equality::disequality")) {
      for (unsigned i = ref.d_mergesStart; i < ref.d_mergesEnd; ++i)
      {
        TNode lhs = d_nodes[d_deducedDisequalityReasons[i].first];
        TNode rhs = d_nodes[d_deducedDisequalityReasons[i].second];
        Debug("equality::disequality") << d_name << "::eq::storePropagatedDisequality(): because " << lhs << " == " << rhs << std::endl;
      }
    }

    // Store for backtracking
    d_deducedDisequalities.push_back(pair1);
    d_deducedDisequalitiesSize = d_deducedDisequalities.size();
    d_deducedDisequalityReasonsSize = d_deducedDisequalityReasons.size();
    // Store the proof reference
    d_disequalityReasonsMap[pair1] = ref;
    d_disequalityReasonsMap[pair2] = ref;
  } else {
    Assert(d_disequalityReasonsMap.find(pair1) != d_disequalityReasonsMap.end())
        << "You must provide a proof initially";
  }
}

void EqualityEngine::getDisequalities(bool allowConstants,
                                      EqualityNodeId classId,
                                      TheoryIdSet inputTags,
                                      TaggedEqualitiesSet& out)
{
  // Must be empty on input
  Assert(out.size() == 0);
  // The class we are looking for, shouldn't have any of the tags we are looking for already set
  Assert(d_nodeIndividualTrigger[classId] == null_set_id
         || TheoryIdSetUtil::setIntersection(
                getTriggerTermSet(d_nodeIndividualTrigger[classId]).d_tags,
                inputTags)
                == 0);

  if (inputTags == 0) {
    return;
  }

  // Set of already (through disequalities) visited equivalence classes
  std::set<EqualityNodeId> alreadyVisited;

  // Go through the equivalence class
  EqualityNodeId currentId = classId;
  do {

    Debug("equality::trigger") << d_name << "::getDisequalities() : going through uselist of " << d_nodes[currentId] << std::endl;

    // Current node in the equivalence class
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Go through the uselist and look for disequalities
    UseListNodeId currentUseId = currentNode.getUseList();
    while (currentUseId != null_uselist_id) {
      UseListNode& useListNode = d_useListNodes[currentUseId];
      EqualityNodeId funId = useListNode.getApplicationId();

      Debug("equality::trigger") << d_name << "::getDisequalities() : checking " << d_nodes[funId] << std::endl;

      const FunctionApplication& fun =
          d_applications[useListNode.getApplicationId()].d_original;
      // If it's an equality asserted to false, we do the work
      if (fun.isEquality() && getEqualityNode(funId).getFind() == getEqualityNode(d_false).getFind()) {
        // Get the other equality member
        bool lhs = false;
        EqualityNodeId toCompare = fun.d_b;
        if (toCompare == currentId) {
          toCompare = fun.d_a;
          lhs = true;
        }
        // Representative of the other member
        EqualityNodeId toCompareRep = getEqualityNode(toCompare).getFind();
        if (toCompareRep == classId) {
          // We're in conflict, so we will send it out from merge
          out.clear();
          return;
        }
        // Check if we already have this one
        if (alreadyVisited.count(toCompareRep) == 0) {
          // Mark as visited
          alreadyVisited.insert(toCompareRep);
          // Get the trigger set
          TriggerTermSetRef toCompareTriggerSetRef = d_nodeIndividualTrigger[toCompareRep];
          // We only care if we're not both constants and there are trigger terms in the other class
          if ((allowConstants || !d_isConstant[toCompareRep]) && toCompareTriggerSetRef != null_set_id) {
            // Tags of the other gey
            TriggerTermSet& toCompareTriggerSet = getTriggerTermSet(toCompareTriggerSetRef);
            // We only care if there are things in inputTags that is also in toCompareTags
            TheoryIdSet commonTags = TheoryIdSetUtil::setIntersection(
                inputTags, toCompareTriggerSet.d_tags);
            if (commonTags) {
              out.push_back(TaggedEquality(funId, toCompareTriggerSetRef, lhs));
            }
          }
        }
      }
      // Go to the next one in the use list
      currentUseId = useListNode.getNext();
    }
    // Next in equivalence class
    currentId = currentNode.getNext();
  } while (!d_done && currentId != classId);

}

bool EqualityEngine::propagateTriggerTermDisequalities(
    TheoryIdSet tags,
    TriggerTermSetRef triggerSetRef,
    const TaggedEqualitiesSet& disequalitiesToNotify)
{
  // No tags, no food
  if (!tags) {
    return !d_done;
  }

  Assert(triggerSetRef != null_set_id);

  // This is the class trigger set
  const TriggerTermSet& triggerSet = getTriggerTermSet(triggerSetRef);
  // Go through the disequalities and notify
  TaggedEqualitiesSet::const_iterator it = disequalitiesToNotify.begin();
  TaggedEqualitiesSet::const_iterator it_end = disequalitiesToNotify.end();
  for (; !d_done && it != it_end; ++ it) {
    // The information about the equality that is asserted to false
    const TaggedEquality& disequalityInfo = *it;
    const TriggerTermSet& disequalityTriggerSet =
        getTriggerTermSet(disequalityInfo.d_triggerSetRef);
    TheoryIdSet commonTags =
        TheoryIdSetUtil::setIntersection(disequalityTriggerSet.d_tags, tags);
    Assert(commonTags);
    // This is the actual function
    const FunctionApplication& fun =
        d_applications[disequalityInfo.d_equalityId].d_original;
    // Figure out who we are comparing to in the original equality
    EqualityNodeId toCompare = disequalityInfo.d_lhs ? fun.d_a : fun.d_b;
    EqualityNodeId myCompare = disequalityInfo.d_lhs ? fun.d_b : fun.d_a;
    if (getEqualityNode(toCompare).getFind() == getEqualityNode(myCompare).getFind()) {
      // We're propagating a != a, which means we're inconsistent, just bail and let it go into
      // a regular conflict
      return !d_done;
    }
    // Go through the tags, and add the disequalities
    TheoryId currentTag;
    while (
        !d_done
        && ((currentTag = TheoryIdSetUtil::setPop(commonTags)) != THEORY_LAST))
    {
      // Get the tag representative
      EqualityNodeId tagRep = disequalityTriggerSet.getTrigger(currentTag);
      EqualityNodeId myRep = triggerSet.getTrigger(currentTag);
      // Propagate
      if (!hasPropagatedDisequality(currentTag, myRep, tagRep)) {
        // Construct the proof if not there already
        if (!hasPropagatedDisequality(myRep, tagRep)) {
          d_deducedDisequalityReasons.push_back(EqualityPair(myCompare, myRep));
          d_deducedDisequalityReasons.push_back(EqualityPair(toCompare, tagRep));
          d_deducedDisequalityReasons.push_back(
              EqualityPair(disequalityInfo.d_equalityId, d_falseId));
        }
        // Store the propagation
        storePropagatedDisequality(currentTag, myRep, tagRep);
        // Notify
        if (d_performNotify) {
          if (!d_notify.eqNotifyTriggerTermEquality(currentTag, d_nodes[myRep], d_nodes[tagRep], false)) {
            d_done = true;
          }
        }
      }
    }
  }

  return !d_done;
}

TheoryIdSet EqualityEngine::TriggerTermSet::hasTrigger(TheoryId tag) const
{
  return TheoryIdSetUtil::setContains(tag, d_tags);
}

EqualityNodeId EqualityEngine::TriggerTermSet::getTrigger(TheoryId tag) const
{
  return d_triggers[TheoryIdSetUtil::setIndex(tag, d_tags)];
}

} // Namespace uf
} // Namespace theory
} // Namespace CVC4
