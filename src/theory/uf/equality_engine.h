/*********************                                                        */
/*! \file equality_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include <deque>
#include <queue>
#include <unordered_map>
#include <vector>

#include "base/output.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "expr/kind_map.h"
#include "expr/node.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine_types.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace eq {


class EqProof;
class EqClassesIterator;
class EqClassIterator;

/**
 * Interface for equality engine notifications. All the notifications
 * are safe as TNodes, but not necessarily for negations.
 */
class EqualityEngineNotify {

  friend class EqualityEngine;

public:

  virtual ~EqualityEngineNotify() {};

  /**
   * Notifies about a trigger equality that became true or false.
   *
   * @param equality the equality that became true or false
   * @param value the value of the equality
   */
  virtual bool eqNotifyTriggerEquality(TNode equality, bool value) = 0;

  /**
   * Notifies about a trigger predicate that became true or false.
   *
   * @param predicate the trigger predicate that became true or false
   * @param value the value of the predicate
   */
  virtual bool eqNotifyTriggerPredicate(TNode predicate, bool value) = 0;

  /**
   * Notifies about the merge of two trigger terms.
   *
   * @param tag the theory that both triggers were tagged with
   * @param t1 a term marked as trigger
   * @param t2 a term marked as trigger
   * @param value true if equal, false if dis-equal
   */
  virtual bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) = 0;

  /**
   * Notifies about the merge of two constant terms. After this, all work is suspended and all you
   * can do is ask for explanations.
   *
   * @param t1 a constant term
   * @param t2 a constant term
   */
  virtual void eqNotifyConstantTermMerge(TNode t1, TNode t2) = 0;

  /**
   * Notifies about the creation of a new equality class.
   *
   * @param t the term forming the new class
   */
  virtual void eqNotifyNewClass(TNode t) = 0;

  /**
   * Notifies about the merge of two classes (just before the merge).
   *
   * @param t1 a term
   * @param t2 a term
   */
  virtual void eqNotifyPreMerge(TNode t1, TNode t2) = 0;

  /**
   * Notifies about the merge of two classes (just after the merge).
   *
   * @param t1 a term
   * @param t2 a term
   */
  virtual void eqNotifyPostMerge(TNode t1, TNode t2) = 0;

  /**
   * Notifies about the disequality of two terms.
   *
   * @param t1 a term
   * @param t2 a term
   * @param reason the reason
   */
  virtual void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) = 0;

};/* class EqualityEngineNotify */

/**
 * Implementation of the notification interface that ignores all the
 * notifications.
 */
class EqualityEngineNotifyNone : public EqualityEngineNotify {
public:
  bool eqNotifyTriggerEquality(TNode equality, bool value) { return true; }
  bool eqNotifyTriggerPredicate(TNode predicate, bool value) { return true; }
  bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) { return true; }
  void eqNotifyConstantTermMerge(TNode t1, TNode t2) { }
  void eqNotifyNewClass(TNode t) { }
  void eqNotifyPreMerge(TNode t1, TNode t2) { }
  void eqNotifyPostMerge(TNode t1, TNode t2) { }
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
};/* class EqualityEngineNotifyNone */

/**
 * An interface for equality engine notifications during equality path reconstruction.
 * Can be used to add theory-specific logic for, e.g., proof construction.
 */
class PathReconstructionNotify {
public:

  virtual ~PathReconstructionNotify() {}

  virtual void notify(unsigned reasonType, Node reason, Node a, Node b,
                      std::vector<TNode>& equalities, EqProof* proof) const = 0;
};

/**
 * Class for keeping an incremental congruence closure over a set of terms. It provides
 * notifications via an EqualityEngineNotify object.
 */
class EqualityEngine : public context::ContextNotifyObj {

  friend class EqClassesIterator;
  friend class EqClassIterator;

  /** Default implementation of the notification object */
  static EqualityEngineNotifyNone s_notifyNone;

  /**
   * Master equality engine that gets all the equality information from
   * this one, or null if none.
   */
  EqualityEngine* d_masterEqualityEngine;

public:

  /**
   * Initialize the equality engine, given the notification class.
   */
  EqualityEngine(EqualityEngineNotify& notify, context::Context* context, std::string name, bool constantsAreTriggers);

  /**
   * Initialize the equality engine with no notification class.
   */
  EqualityEngine(context::Context* context, std::string name, bool constantsAreTriggers);

  /**
   * Just a destructor.
   */
  virtual ~EqualityEngine();

  /**
   * Set the master equality engine for this one. Master engine will get copies of all
   * the terms and equalities from this engine.
   */
  void setMasterEqualityEngine(EqualityEngine* master);

  /** Statistics about the equality engine instance */
  struct Statistics {
    /** Total number of merges */
    IntStat mergesCount;
    /** Number of terms managed by the system */
    IntStat termsCount;
    /** Number of function terms managed by the system */
    IntStat functionTermsCount;
    /** Number of constant terms managed by the system */
    IntStat constantTermsCount;

    Statistics(std::string name);

    ~Statistics();
  };/* struct EqualityEngine::statistics */

private:

  /** The context we are using */
  context::Context* d_context;

  /** If we are done, we don't except any new assertions */
  context::CDO<bool> d_done;

  /** Whether to notify or not (temporarily disabled on equality checks) */
  bool d_performNotify;

  /** The class to notify when a representative changes for a term */
  EqualityEngineNotify& d_notify;

  /** The map of kinds to be treated as function applications */
  KindMap d_congruenceKinds;

  /** The map of kinds to be treated as interpreted function applications (for evaluation of constants) */
  KindMap d_congruenceKindsInterpreted;

  /** Objects that need to be notified during equality path reconstruction */
  std::map<unsigned, const PathReconstructionNotify*> d_pathReconstructionTriggers;

  /** Map from nodes to their ids */
  std::unordered_map<TNode, EqualityNodeId, TNodeHashFunction> d_nodeIds;

  /** Map from function applications to their ids */
  typedef std::unordered_map<FunctionApplication, EqualityNodeId, FunctionApplicationHashFunction> ApplicationIdsMap;

  /**
   * A map from a pair (a', b') to a function application f(a, b), where a' and b' are the current representatives
   * of a and b.
   */
  ApplicationIdsMap d_applicationLookup;

  /** Application lookups in order, so that we can backtrack. */
  std::vector<FunctionApplication> d_applicationLookups;

  /** Number of application lookups, for backtracking.  */
  context::CDO<DefaultSizeType> d_applicationLookupsCount;

  /**
   * Store the application lookup, with enough information to backtrack
   */
  void storeApplicationLookup(FunctionApplication& funNormalized, EqualityNodeId funId);

  /** Map from ids to the nodes (these need to be nodes as we pick up the operators) */
  std::vector<Node> d_nodes;

  /** A context-dependents count of nodes */
  context::CDO<DefaultSizeType> d_nodesCount;

  /** Map from ids to the applications */
  std::vector<FunctionApplicationPair> d_applications;

  /** Map from ids to the equality nodes */
  std::vector<EqualityNode> d_equalityNodes;

  /** Number of asserted equalities we have so far */
  context::CDO<DefaultSizeType> d_assertedEqualitiesCount;

  /** Memory for the use-list nodes */
  std::vector<UseListNode> d_useListNodes;

  /** A fresh merge reason type to return upon request */
  unsigned d_freshMergeReasonType;

  /**
   * We keep a list of asserted equalities. Not among original terms, but
   * among the class representatives.
   */
  struct Equality {
    /** Left hand side of the equality */
    EqualityNodeId lhs;
    /** Right hand side of the equality */
    EqualityNodeId rhs;
    /** Equality constructor */
    Equality(EqualityNodeId lhs = null_id, EqualityNodeId rhs = null_id)
    : lhs(lhs), rhs(rhs) {}
  };/* struct EqualityEngine::Equality */

  /** The ids of the classes we have merged */
  std::vector<Equality> d_assertedEqualities;

  /** The reasons for the equalities */

  /**
   * An edge in the equality graph. This graph is an undirected graph (both edges added)
   * containing the actual asserted equalities.
   */
  class EqualityEdge {

    // The id of the RHS of this equality
    EqualityNodeId d_nodeId;
    // The next edge
    EqualityEdgeId d_nextId;
    // Type of reason for this equality
    unsigned d_mergeType;
    // Reason of this equality
    TNode d_reason;

  public:

    EqualityEdge():
      d_nodeId(null_edge), d_nextId(null_edge), d_mergeType(MERGED_THROUGH_CONGRUENCE) {}

    EqualityEdge(EqualityNodeId nodeId, EqualityNodeId nextId, unsigned type, TNode reason):
      d_nodeId(nodeId), d_nextId(nextId), d_mergeType(type), d_reason(reason) {}

    /** Returns the id of the next edge */
    EqualityEdgeId getNext() const { return d_nextId; }

    /** Returns the id of the target edge node */
    EqualityNodeId getNodeId() const { return d_nodeId; }

    /** The reason of this edge */
    unsigned getReasonType() const { return d_mergeType; }

    /** The reason of this edge */
    TNode getReason() const { return d_reason; }
  };/* class EqualityEngine::EqualityEdge */

  /**
   * All the equality edges (twice as many as the number of asserted equalities. If an equality
   * t1 = t2 is asserted, the edges added are -> t2, -> t1 (in this order). Hence, having the index
   * of one of the edges you can reconstruct the original equality.
   */
  std::vector<EqualityEdge> d_equalityEdges;

  /**
   * Returns the string representation of the edges.
   */
  std::string edgesToString(EqualityEdgeId edgeId) const;

  /**
   * Map from a node to its first edge in the equality graph. Edges are added to the front of the
   * list which makes the insertion/backtracking easy.
   */
  std::vector<EqualityEdgeId> d_equalityGraph;

  /** Add an edge to the equality graph */
  void addGraphEdge(EqualityNodeId t1, EqualityNodeId t2, unsigned type, TNode reason);

  /** Returns the equality node of the given node */
  EqualityNode& getEqualityNode(TNode node);

  /** Returns the equality node of the given node */
  const EqualityNode& getEqualityNode(TNode node) const;

  /** Returns the equality node of the given node */
  EqualityNode& getEqualityNode(EqualityNodeId nodeId);

  /** Returns the equality node of the given node */
  const EqualityNode& getEqualityNode(EqualityNodeId nodeId) const;

  /** Returns the id of the node */
  EqualityNodeId getNodeId(TNode node) const;

  /**
   * Merge the class2 into class1
   * @return true if ok, false if to break out
   */
  bool merge(EqualityNode& class1, EqualityNode& class2, std::vector<TriggerId>& triggers);

  /** Undo the merge of class2 into class1 */
  void undoMerge(EqualityNode& class1, EqualityNode& class2, EqualityNodeId class2Id);

  /** Backtrack the information if necessary */
  void backtrack();

  /**
   * Trigger that will be updated
   */
  struct Trigger {
    /** The current class id of the LHS of the trigger */
    EqualityNodeId classId;
    /** Next trigger for class */
    TriggerId nextTrigger;

    Trigger(EqualityNodeId classId = null_id, TriggerId nextTrigger = null_trigger)
    : classId(classId), nextTrigger(nextTrigger) {}
  };/* struct EqualityEngine::Trigger */

  /**
   * Vector of triggers. Triggers come in pairs for an
   * equality trigger (t1, t2): one at position 2k for t1, and one at position 2k + 1 for t2. When
   * updating triggers we always know where the other one is (^1).
   */
  std::vector<Trigger> d_equalityTriggers;

  /**
   * Vector of original equalities of the triggers.
   */
  std::vector<TriggerInfo> d_equalityTriggersOriginal;

  /**
   * Context dependent count of triggers
   */
  context::CDO<DefaultSizeType> d_equalityTriggersCount;

  /**
   * Trigger lists per node. The begin id changes as we merge, but the end always points to
   * the actual end of the triggers for this node.
   */
  std::vector<TriggerId> d_nodeTriggers;

  /**
   * Map from ids to whether they are constants (constants are always
   * representatives of their class.
   */
  std::vector<bool> d_isConstant;

  /**
   * Map from ids of proper terms, to the number of non-constant direct subterms. If we update an interpreted
   * application to a constant, we can decrease this value. If we hit 0, we can evaluate the term.
   *
   */
  std::vector<unsigned> d_subtermsToEvaluate;

  /**
   * For nodes that we need to postpone evaluation.
   */
  std::queue<EqualityNodeId> d_evaluationQueue;

  /**
   * Evaluate all terms in the evaluation queue.
   */
  void processEvaluationQueue();

  /** Vector of nodes that evaluate. */
  std::vector<EqualityNodeId> d_subtermEvaluates;

  /** Size of the nodes that evaluate vector. */
  context::CDO<unsigned> d_subtermEvaluatesSize;

  /** Set the node evaluate flag */
  void subtermEvaluates(EqualityNodeId id);

  /**
   * Returns the evaluation of the term when all (direct) children are replaced with
   * the constant representatives.
   */
  Node evaluateTerm(TNode node);

  /**
   * Returns true if it's a constant
   */
  bool isConstant(EqualityNodeId id) const {
    return d_isConstant[getEqualityNode(id).getFind()];
  }

  /**
   * Map from ids to whether they are Boolean.
   */
  std::vector<bool> d_isEquality;

  /**
   * Map from ids to whether the nods is internal. An internal node is a node
   * that corresponds to a partially currified node, for example.
   */
  std::vector<bool> d_isInternal;

  /**
   * Adds the trigger with triggerId to the beginning of the trigger list of the node with id nodeId.
   */
  void addTriggerToList(EqualityNodeId nodeId, TriggerId triggerId);

  /** Statistics */
  Statistics d_stats;

  /** Add a new function application node to the database, i.e APP t1 t2 */
  EqualityNodeId newApplicationNode(TNode original, EqualityNodeId t1, EqualityNodeId t2, FunctionApplicationType type);

  /** Add a new node to the database */
  EqualityNodeId newNode(TNode t);

  /** Propagation queue */
  std::deque<MergeCandidate> d_propagationQueue;

  /** Enqueue to the propagation queue */
  void enqueue(const MergeCandidate& candidate, bool back = true);

  /** Do the propagation */
  void propagate();

  /** Are we in propagate */
  bool d_inPropagate;

  /**
   * Get an explanation of the equality t1 = t2. Returns the asserted equalities that
   * imply t1 = t2. Returns TNodes as the assertion equalities should be hashed somewhere
   * else.
   */
  void getExplanation(EqualityEdgeId t1Id, EqualityNodeId t2Id, std::vector<TNode>& equalities, EqProof * eqp) const;

  /**
   * Print the equality graph.
   */
  void debugPrintGraph() const;

  /** The true node */
  Node d_true;
  /** True node id */
  EqualityNodeId d_trueId;

  /** The false node */
  Node d_false;
  /** False node id */
  EqualityNodeId d_falseId;

  /**
   * Adds an equality of terms t1 and t2 to the database.
   */
  void assertEqualityInternal(TNode t1, TNode t2, TNode reason, unsigned pid = MERGED_THROUGH_EQUALITY);

  /**
   * Adds a trigger equality to the database with the trigger node and polarity for notification.
   */
  void addTriggerEqualityInternal(TNode t1, TNode t2, TNode trigger, bool polarity);

  /**
   * This method gets called on backtracks from the context manager.
   */
  void contextNotifyPop() {
    backtrack();
  }

  /**
   * Constructor initialization stuff.
   */
  void init();

  /** Set of trigger terms */
  struct TriggerTermSet {
    /** Set of theories in this set */
    Theory::Set tags;
    /** The trigger terms */
    EqualityNodeId triggers[0];
    /** Returns the theory tags */
    Theory::Set hasTrigger(TheoryId tag) const { return Theory::setContains(tag, tags); }
    /** Returns a trigger by tag */
    EqualityNodeId getTrigger(TheoryId tag) const {
      return triggers[Theory::setIndex(tag, tags)];
    }
  };/* struct EqualityEngine::TriggerTermSet */

  /** Are the constants triggers */
  bool d_constantsAreTriggers;

  /** The information about trigger terms is stored in this easily maintained memory. */
  char* d_triggerDatabase;

  /** Allocated size of the trigger term database */
  DefaultSizeType d_triggerDatabaseAllocatedSize;

  /** Reference for the trigger terms set */
  typedef DefaultSizeType TriggerTermSetRef;

  /** Null reference */
  static const TriggerTermSetRef null_set_id = (TriggerTermSetRef)(-1);

  /** Create new trigger term set based on the internally set information */
  TriggerTermSetRef newTriggerTermSet(Theory::Set newSetTags, EqualityNodeId* newSetTriggers, unsigned newSetTriggersSize);

  /** Get the trigger set give a reference */
  TriggerTermSet& getTriggerTermSet(TriggerTermSetRef ref) {
    Assert(ref < d_triggerDatabaseSize);
    return *(reinterpret_cast<TriggerTermSet*>(d_triggerDatabase + ref));
  }

  /** Get the trigger set give a reference */
  const TriggerTermSet& getTriggerTermSet(TriggerTermSetRef ref) const {
    Assert(ref < d_triggerDatabaseSize);
    return *(reinterpret_cast<const TriggerTermSet*>(d_triggerDatabase + ref));
  }

  /** Used part of the trigger term database */
  context::CDO<DefaultSizeType> d_triggerDatabaseSize;

  struct TriggerSetUpdate {
    EqualityNodeId classId;
    TriggerTermSetRef oldValue;
    TriggerSetUpdate(EqualityNodeId classId = null_id, TriggerTermSetRef oldValue = null_set_id)
    : classId(classId), oldValue(oldValue) {}
  };/* struct EqualityEngine::TriggerSetUpdate */

  /**
   * List of trigger updates for backtracking.
   */
  std::vector<TriggerSetUpdate> d_triggerTermSetUpdates;

  /**
   * Size of the individual triggers list.
   */
  context::CDO<unsigned> d_triggerTermSetUpdatesSize;

  /**
   * Map from ids to the individual trigger set representatives.
   */
  std::vector<TriggerTermSetRef> d_nodeIndividualTrigger;

  typedef std::unordered_map<EqualityPair, DisequalityReasonRef, EqualityPairHashFunction> DisequalityReasonsMap;

  /**
   * A map from pairs of disequal terms, to the reason why we deduced they are disequal.
   */
  DisequalityReasonsMap d_disequalityReasonsMap;

  /**
   * A list of all the disequalities we deduced.
   */
  std::vector<EqualityPair> d_deducedDisequalities;

  /**
   * Context dependent size of the deduced disequalities
   */
  context::CDO<size_t> d_deducedDisequalitiesSize;

  /**
   * For each disequality deduced, we add the pairs of equivalences needed to explain it.
   */
  std::vector<EqualityPair> d_deducedDisequalityReasons;

  /**
   * Size of the memory for disequality reasons.
   */
  context::CDO<size_t> d_deducedDisequalityReasonsSize;

  /**
   * Map from equalities to the tags that have received the notification.
   */
  typedef context::CDHashMap<EqualityPair, Theory::Set, EqualityPairHashFunction> PropagatedDisequalitiesMap;
  PropagatedDisequalitiesMap d_propagatedDisequalities;

  /**
   * Has this equality been propagated to anyone.
   */
  bool hasPropagatedDisequality(EqualityNodeId lhsId, EqualityNodeId rhsId) const;

  /**
   * Has this equality been propagated to the tag owner.
   */
  bool hasPropagatedDisequality(TheoryId tag, EqualityNodeId lhsId, EqualityNodeId rhsId) const;

  /**
   * Stores a propagated disequality for explanation purposes and remembers the reasons. The
   * reasons should be pushed on the reasons vector.
   */
  void storePropagatedDisequality(TheoryId tag, EqualityNodeId lhsId, EqualityNodeId rhsId);

  /**
   * An equality tagged with a set of tags.
   */
  struct TaggedEquality {
    /** Id of the equality */
    EqualityNodeId equalityId;
    /** TriggerSet reference for the class of one of the sides */
    TriggerTermSetRef triggerSetRef;
    /** Is trigger equivalent to the lhs (rhs otherwise) */
    bool lhs;

    TaggedEquality(EqualityNodeId equalityId = null_id, TriggerTermSetRef triggerSetRef = null_set_id, bool lhs = true)
    : equalityId(equalityId), triggerSetRef(triggerSetRef), lhs(lhs) {}
  };

  /** A map from equivalence class id's to tagged equalities */
  typedef std::vector<TaggedEquality> TaggedEqualitiesSet;

  /**
   * Returns a set of equalities that have been asserted false where one side of the equality
   * belongs to the given equivalence class. The equalities are restricted to the ones where
   * one side of the equality is in the tags set, but the other one isn't. Each returned
   * dis-equality is associated with the tags that are the subset of the input tags, such that
   * exactly one side of the equality is not in the set yet.
   *
   * @param classId the equivalence class to search
   * @param inputTags the tags to filter the equalities
   * @param out the output equalities, as described above
   */
  void getDisequalities(bool allowConstants, EqualityNodeId classId, Theory::Set inputTags, TaggedEqualitiesSet& out);

  /**
   * Propagates the remembered disequalities with given tags the original triggers for those tags,
   * and the set of disequalities produced by above.
   */
  bool propagateTriggerTermDisequalities(Theory::Set tags,
    TriggerTermSetRef triggerSetRef, const TaggedEqualitiesSet& disequalitiesToNotify);

  /** Name of the equality engine */
  std::string d_name;

  /** The internal addTerm */
  void addTermInternal(TNode t, bool isOperator = false);

public:

  /**
   * Adds a term to the term database.
   */
  void addTerm(TNode t) {
    addTermInternal(t, false);
  }

  /**
   * Add a kind to treat as function applications.
   */
  void addFunctionKind(Kind fun, bool interpreted = false);

  /**
   * Returns true if this kind is used for congruence closure.
   */
  bool isFunctionKind(Kind fun) const {
    return d_congruenceKinds.tst(fun);
  }

  /**
   * Returns true if this kind is used for congruence closure + evaluation of constants.
   */
  bool isInterpretedFunctionKind(Kind fun) const {
    return d_congruenceKindsInterpreted.tst(fun);
  }

  /**
   * Check whether the node is already in the database.
   */
  bool hasTerm(TNode t) const;

  /**
   * Adds a predicate p with given polarity. The predicate asserted
   * should be in the congruence closure kinds (otherwise it's
   * useless).
   *
   * @param p the (non-negated) predicate
   * @param polarity true if asserting the predicate, false if
   *                 asserting the negated predicate
   * @param reason the reason to keep for building explanations
   */
  void assertPredicate(TNode p, bool polarity, TNode reason, unsigned pid = MERGED_THROUGH_EQUALITY);

  /**
   * Adds predicate p and q and makes them equal.
   */
  void mergePredicates(TNode p, TNode q, TNode reason);

  /**
   * Adds an equality eq with the given polarity to the database.
   *
   * @param eq the (non-negated) equality
   * @param polarity true if asserting the equality, false if
   *                 asserting the negated equality
   * @param reason the reason to keep for building explanations
   */
  void assertEquality(TNode eq, bool polarity, TNode reason, unsigned pid = MERGED_THROUGH_EQUALITY);

  /**
   * Returns the current representative of the term t.
   */
  TNode getRepresentative(TNode t) const;

  /**
   * Add all the terms where the given term appears as a first child
   * (directly or implicitly).
   */
  void getUseListTerms(TNode t, std::set<TNode>& output);

  /**
   * Get an explanation of the equality t1 = t2 being true or false.
   * Returns the reasons (added when asserting) that imply it
   * in the assertions vector.
   */
  void explainEquality(TNode t1, TNode t2, bool polarity, std::vector<TNode>& assertions, EqProof * eqp = NULL) const;

  /**
   * Get an explanation of the predicate being true or false.
   * Returns the reasons (added when asserting) that imply imply it
   * in the assertions vector.
   */
  void explainPredicate(TNode p, bool polarity, std::vector<TNode>& assertions, EqProof * eqp = NULL) const;

  /**
   * Add term to the set of trigger terms with a corresponding tag. The notify class will get
   * notified when two trigger terms with the same tag become equal or dis-equal. The notification
   * will not happen on all the terms, but only on the ones that are represent the class. Note that
   * a term can be added more than once with different tags, and each tag appearance will merit
   * it's own notification.
   *
   * @param t the trigger term
   * @param theoryTag tag for this trigger (do NOT use THEORY_LAST)
   */
  void addTriggerTerm(TNode t, TheoryId theoryTag);

  /**
   * Returns true if t is a trigger term or in the same equivalence
   * class as some other trigger term.
   */
  bool isTriggerTerm(TNode t, TheoryId theoryTag) const;

  /**
   * Returns the representative trigger term of the given term.
   *
   * @param t the term to check where isTriggerTerm(t) should be true
   */
  TNode getTriggerTermRepresentative(TNode t, TheoryId theoryTag) const;

  /**
   * Adds a notify trigger for equality. When equality becomes true eqNotifyTriggerEquality
   * will be called with value = true, and when equality becomes false eqNotifyTriggerEquality
   * will be called with value = false.
   */
  void addTriggerEquality(TNode equality);

  /**
   * Adds a notify trigger for the predicate p. When the predicate becomes true
   * eqNotifyTriggerPredicate will be called with value = true, and when equality becomes false
   * eqNotifyTriggerPredicate will be called with value = false.
   */
  void addTriggerPredicate(TNode predicate);

  /**
   * Returns true if the two terms are equal. Requires both terms to
   * be in the database.
   */
  bool areEqual(TNode t1, TNode t2) const;

  /**
   * Check whether the two term are dis-equal. Requires both terms to
   * be in the database.
   */
  bool areDisequal(TNode t1, TNode t2, bool ensureProof) const;

  /**
   * Return the number of nodes in the equivalence class containing t
   * Adds t if not already there.
   */
  size_t getSize(TNode t);

  /**
   * Returns true if the engine is in a consistent state.
   */
  bool consistent() const { return !d_done; }

  /**
   * Marks an object for merge type based notification during equality path reconstruction.
   */
  void addPathReconstructionTrigger(unsigned trigger, const PathReconstructionNotify* notify);

  /**
   * Returns a fresh merge reason type tag for the client to use.
   */
  unsigned getFreshMergeReasonType();
};

/**
 * Iterator to iterate over the equivalence classes.
 */
class EqClassesIterator {
  const eq::EqualityEngine* d_ee;
  size_t d_it;
public:
  EqClassesIterator();
  EqClassesIterator(const eq::EqualityEngine* ee);
  Node operator*() const;
  bool operator==(const EqClassesIterator& i) const;
  bool operator!=(const EqClassesIterator& i) const;
  EqClassesIterator& operator++();
  EqClassesIterator operator++(int);
  bool isFinished() const;
};/* class EqClassesIterator */

/**
 * Iterator to iterate over the equivalence class members.
 */
class EqClassIterator {
  const eq::EqualityEngine* d_ee;
  /** Starting node */
  EqualityNodeId d_start;
  /** Current node */
  EqualityNodeId d_current;
public:
  EqClassIterator();
  EqClassIterator(Node eqc, const eq::EqualityEngine* ee);
  Node operator*() const;
  bool operator==(const EqClassIterator& i) const;
  bool operator!=(const EqClassIterator& i) const;
  EqClassIterator& operator++();
  EqClassIterator operator++(int);
  bool isFinished() const;
};/* class EqClassIterator */

class EqProof
{
public:
  class PrettyPrinter {
  public:
    virtual ~PrettyPrinter() {}
    virtual std::string printTag(unsigned tag) = 0;
  };

  EqProof() : d_id(MERGED_THROUGH_REFLEXIVITY){}
  unsigned d_id;
  Node d_node;
  std::vector< EqProof * > d_children;
  void debug_print(const char * c, unsigned tb = 0, PrettyPrinter* prettyPrinter = NULL) const;
};/* class EqProof */

} // Namespace eq
} // Namespace theory
} // Namespace CVC4
