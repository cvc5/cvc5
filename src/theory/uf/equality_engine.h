/*********************                                                        */
/*! \file equality_engine.h
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

#include <queue>
#include <vector>
#include <ext/hash_map>
#include <sstream>

#include "expr/node.h"
#include "expr/kind_map.h"
#include "context/cdo.h"
#include "util/output.h"
#include "util/stats.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace uf {

/** Id of the node */
typedef size_t EqualityNodeId;

/** Id of the use list */
typedef size_t UseListNodeId;

/** The trigger ids */
typedef size_t TriggerId;

/** The equality edge ids */
typedef size_t EqualityEdgeId;

/** The null node */
static const EqualityNodeId null_id = (size_t)(-1);

/** The null use list node */
static const EqualityNodeId null_uselist_id = (size_t)(-1);

/** The null trigger */
static const TriggerId null_trigger = (size_t)(-1);

/** The null edge id */
static const EqualityEdgeId null_edge = (size_t)(-1);

/**
 * A reason for a merge. Either an equality x = y, or a merge of two
 * function applications f(x1, x2), f(y1, y2)
 */
enum MergeReasonType {
  MERGED_THROUGH_CONGRUENCE,
  MERGED_THROUGH_EQUALITY
};

inline std::ostream& operator << (std::ostream& out, MergeReasonType reason) {
  switch (reason) {
  case MERGED_THROUGH_CONGRUENCE:
    out << "c";
    break;
  case MERGED_THROUGH_EQUALITY:
    out << "e";
    break;
  default:
    Unreachable();
  }
  return out;
}

/** A node in the uselist */
class UseListNode {

private:

  /** The id of the application node where this representative is at */
  EqualityNodeId d_applicationId;

  /** The next one in the class */
  UseListNodeId d_nextUseListNodeId;

public:

  /**
   * Creates a new node, which is in a list of it's own.
   */
  UseListNode(EqualityNodeId nodeId = null_id, UseListNodeId nextId = null_uselist_id)
  : d_applicationId(nodeId), d_nextUseListNodeId(nextId) {}

  /**
   * Returns the next node in the circular list.
   */
  UseListNodeId getNext() const {
    return d_nextUseListNodeId;
  }

  /**
   * Returns the id of the function application.
   */
  EqualityNodeId getApplicationId() const {
    return d_applicationId;
  }
};


class EqualityNode {

private:

  /** The size of this equivalence class (if it's a representative) */
  size_t d_size;

  /** The id (in the eq-manager) of the representative equality node */
  EqualityNodeId d_findId;

  /** The next equality node in this class */
  EqualityNodeId d_nextId;

  /** The use list of this node */
  UseListNodeId d_useList;

public:

  /**
   * Creates a new node, which is in a list of it's own.
   */
  EqualityNode(EqualityNodeId nodeId = null_id)
  : d_size(1), 
    d_findId(nodeId), 
    d_nextId(nodeId), 
    d_useList(null_uselist_id)
  {}

  /**
   * Retuerns the uselist.
   */
  UseListNodeId getUseList() const {
    return d_useList;
  }

  /**
   * Returns the next node in the class circular list.
   */
  EqualityNodeId getNext() const {
    return d_nextId;
  }

  /**
   * Returns the size of this equivalence class (only valid if this is the representative).
   */
  size_t getSize() const {
    return d_size;
  }

  /**
   * Merges the two lists. If add size is true the size of this node is increased by the size of
   * the other node, otherwise the size is decreased by the size of the other node.
   */
  template<bool addSize>
  void merge(EqualityNode& other) {
    EqualityNodeId tmp = d_nextId; d_nextId = other.d_nextId; other.d_nextId = tmp;
    if (addSize) {
      d_size += other.d_size;
    } else {
      d_size -= other.d_size;
    }
  }

  /**
   * Returns the class representative.
   */
  EqualityNodeId getFind() const { return d_findId; }

  /**
   * Set the class representative.
   */
  void setFind(EqualityNodeId findId) { d_findId = findId; }

  /**
   * Note that this node is used in a function a application funId.
   */
  template<typename memory_class>
  void usedIn(EqualityNodeId funId, memory_class& memory) {
    UseListNodeId newUseId = memory.size();
    memory.push_back(UseListNode(funId, d_useList));
    d_useList = newUseId;
  }

  /**
   * For backtracking: remove the first element from the uselist and pop the memory.
   */
  template<typename memory_class>
  void removeTopFromUseList(memory_class& memory) {
    Assert ((int)d_useList == (int)memory.size() - 1);
    d_useList = memory.back().getNext();
    memory.pop_back();
  }
};

template <typename NotifyClass>
class EqualityEngine : public context::ContextNotifyObj {

public:

  /** Statistics about the equality engine instance */
  struct Statistics {
    /** Total number of merges */
    IntStat mergesCount;
    /** Number of terms managed by the system */
    IntStat termsCount;
    /** Number of function terms managed by the system */
    IntStat functionTermsCount;

    Statistics(std::string name)
    : mergesCount(name + "::mergesCount", 0),
      termsCount(name + "::termsCount", 0),
      functionTermsCount(name + "::functionTermsCount", 0)
    {
      StatisticsRegistry::registerStat(&mergesCount);
      StatisticsRegistry::registerStat(&termsCount);
      StatisticsRegistry::registerStat(&functionTermsCount);
    }

    ~Statistics() {
      StatisticsRegistry::unregisterStat(&mergesCount);
      StatisticsRegistry::unregisterStat(&termsCount);
      StatisticsRegistry::unregisterStat(&functionTermsCount);
    }
  };

  /**
   * f(a,b)
   */
  struct FunctionApplication {
    EqualityNodeId a, b;
    FunctionApplication(EqualityNodeId a = null_id, EqualityNodeId b = null_id):
      a(a), b(b) {}
    bool operator == (const FunctionApplication& other) const {
      return a == other.a && b == other.b;
    }
    bool isApplication() const {
      return a != null_id && b != null_id;
    }
  };

  struct FunctionApplicationHashFunction {
    size_t operator () (const FunctionApplication& app) const {
      size_t hash = 0;
      hash = 0x9e3779b9 + app.a;
      hash ^= 0x9e3779b9 + app.b + (hash << 6) + (hash >> 2);
      return hash;
    }
  };

private:

  /** The context we are using */
  context::Context* d_context;

  /** Whether to notify or not (temporarily disabled on equality checks) */
  bool d_performNotify;

  /** The class to notify when a representative changes for a term */
  NotifyClass d_notify;

  /** The map of kinds to be treated as function applications */
  KindMap d_congruenceKinds;

  /** Map from nodes to their ids */
  __gnu_cxx::hash_map<TNode, EqualityNodeId, TNodeHashFunction> d_nodeIds;

  /** Map from function applications to their ids */
  typedef __gnu_cxx::hash_map<FunctionApplication, EqualityNodeId, FunctionApplicationHashFunction> ApplicationIdsMap;

  /**
   * A map from a pair (a', b') to a function application f(a, b), where a' and b' are the current representatives
   * of a and b.
   */
  ApplicationIdsMap d_applicationLookup;

  /** Map from ids to the nodes (these need to be nodes as we pick-up the opreators) */
  std::vector<Node> d_nodes;

  /** A context-dependents count of nodes */
  context::CDO<size_t> d_nodesCount;

  /** Map from ids to the applications */
  std::vector<FunctionApplication> d_applications;

  /** Map from ids to the equality nodes */
  std::vector<EqualityNode> d_equalityNodes;

  /** Number of asserted equalities we have so far */
  context::CDO<size_t> d_assertedEqualitiesCount;

  /** Memory for the use-list nodes */
  std::vector<UseListNode> d_useListNodes;

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
  };

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
    MergeReasonType d_mergeType;
    // Reason of this equality
    TNode d_reason;

  public:

    EqualityEdge():
      d_nodeId(null_edge), d_nextId(null_edge), d_mergeType(MERGED_THROUGH_CONGRUENCE) {}

    EqualityEdge(EqualityNodeId nodeId, EqualityNodeId nextId, MergeReasonType type, TNode reason):
      d_nodeId(nodeId), d_nextId(nextId), d_mergeType(type), d_reason(reason) {}

    /** Returns the id of the next edge */
    EqualityEdgeId getNext() const { return d_nextId; }

    /** Returns the id of the target edge node */
    EqualityNodeId getNodeId() const { return d_nodeId; }

    /** The reason of this edge */
    MergeReasonType getReasonType() const { return d_mergeType; }

    /** The reason of this edge */
    TNode getReason() const { return d_reason; }
};

  /**
   * All the equality edges (twice as many as the number of asserted equalities. If an equality
   * t1 = t2 is asserted, the edges added are -> t2, -> t1 (in this order). Hance, having the index
   * of one of the edges you can reconstruct the original equality.
   */
  std::vector<EqualityEdge> d_equalityEdges;

  /**
   * Returns the string representation of the edges.
   */
  std::string edgesToString(EqualityEdgeId edgeId) const;

  /**
   * Map from a node to it's first edge in the equality graph. Edges are added to the front of the
   * list which makes the insertion/backtracking easy.
   */
  std::vector<EqualityEdgeId> d_equalityGraph;

  /** Add an edge to the equality graph */
  void addGraphEdge(EqualityNodeId t1, EqualityNodeId t2, MergeReasonType type, TNode reason);

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

  /** Merge the class2 into class1 */
  void merge(EqualityNode& class1, EqualityNode& class2, std::vector<TriggerId>& triggers);

  /** Undo the mereg of class2 into class1 */
  void undoMerge(EqualityNode& class1, EqualityNode& class2, EqualityNodeId class2Id);

  /** Backtrack the information if necessary */
  void backtrack();

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

  /**
   * Trigger that will be updated
   */
  struct Trigger {
    /** The current class id of the LHS of the trigger */
    EqualityNodeId classId;
    /** Next trigger for class 1 */
    TriggerId nextTrigger;

    Trigger(EqualityNodeId classId = null_id, TriggerId nextTrigger = null_trigger)
    : classId(classId), nextTrigger(nextTrigger) {}
  };

  /**
   * Vector of triggers. Triggers come in pairs for an
   * equality trigger (t1, t2): one at position 2k for t1, and one at position 2k + 1 for t2. When
   * updating triggers we always know where the other one is (^1).
   */
  std::vector<Trigger> d_equalityTriggers;

  /**
   * Vector of original equalities of the triggers.
   */
  std::vector<Node> d_equalityTriggersOriginal;

  /**
   * Context dependent count of triggers
   */
  context::CDO<size_t> d_equalityTriggersCount;

  /**
   * Trigger lists per node. The begin id changes as we merge, but the end always points to
   * the actual end of the triggers for this node.
   */
  std::vector<TriggerId> d_nodeTriggers;

  /**
   * List of terms that are marked as individual triggers.
   */
  std::vector<EqualityNodeId> d_individualTriggers;

  /**
   * Size of the individual triggers list.
   */
  context::CDO<unsigned> d_individualTriggersSize;

  /** 
   * Map from ids to the individual trigger id representative. 
   */
  std::vector<EqualityNodeId> d_nodeIndividualTrigger;

  /**
   * Adds the trigger with triggerId to the beginning of the trigger list of the node with id nodeId.
   */
  void addTriggerToList(EqualityNodeId nodeId, TriggerId triggerId);

  /** Statistics */
  Statistics d_stats;

  /** Add a new function application node to the database, i.e APP t1 t2 */
  EqualityNodeId newApplicationNode(TNode original, EqualityNodeId t1, EqualityNodeId t2);

  /** Add a new node to the database */
  EqualityNodeId newNode(TNode t, bool isApplication);

  struct MergeCandidate {
    EqualityNodeId t1Id, t2Id;
    MergeReasonType type;
    TNode reason;
    MergeCandidate(EqualityNodeId x, EqualityNodeId y, MergeReasonType type, TNode reason):
      t1Id(x), t2Id(y), type(type), reason(reason) {}

    std::string toString(EqualityEngine& eqEngine) const {
      std::stringstream ss;
      ss << eqEngine.d_nodes[t1Id] << " = " << eqEngine.d_nodes[t2Id] << ", " << type;
      return ss.str();
    }
  };

  /** Propagation queue */
  std::queue<MergeCandidate> d_propagationQueue;

  /** Enqueue to the propagation queue */
  void enqueue(const MergeCandidate& candidate);

  /** Do the propagation */
  void propagate();

  /**
   * Get an explanation of the equality t1 = t2. Returns the asserted equalities that
   * imply t1 = t2. Returns TNodes as the assertion equalities should be hashed somewhere
   * else. 
   */
  void getExplanation(EqualityEdgeId t1Id, EqualityNodeId t2Id, std::vector<TNode>& equalities) const;

  /**
   * Print the equality graph.
   */
  void debugPrintGraph() const;

  /** The true node */
  Node d_true;
  /** The false node */
  Node d_false;

public:

  /**
   * Initialize the equality engine, given the owning class. This will initialize the notifier with
   * the owner information.
   */
  EqualityEngine(NotifyClass& notify, context::Context* context, std::string name)
  : ContextNotifyObj(context),
    d_context(context),
    d_performNotify(true),
    d_notify(notify),
    d_nodesCount(context, 0),
    d_assertedEqualitiesCount(context, 0),
    d_equalityTriggersCount(context, 0),
    d_individualTriggersSize(context, 0),
    d_stats(name)
  {
    Debug("equality") << "EqualityEdge::EqualityEngine(): id_null = " << +null_id << std::endl;
    Debug("equality") << "EqualityEdge::EqualityEngine(): edge_null = " << +null_edge << std::endl;
    Debug("equality") << "EqualityEdge::EqualityEngine(): trigger_null = " << +null_trigger << std::endl;
    d_true = NodeManager::currentNM()->mkConst<bool>(true);
    d_false = NodeManager::currentNM()->mkConst<bool>(false);
  }

  /**
   * Just a destructor.
   */
  virtual ~EqualityEngine() throw(AssertionException) {}

  /**
   * This method gets called on backtracks from the context manager.
   */
  void notify() {
    backtrack();
  }

  /**
   * Adds a term to the term database.
   */
  void addTerm(TNode t);

  /**
   * Add a kind to treat as function applications.
   */
  void addFunctionKind(Kind fun) {
    d_congruenceKinds |= fun;
  }

  /**
   * Adds a function application term to the database.
   */

  /**
   * Check whether the node is already in the database.
   */
  bool hasTerm(TNode t) const;

  /**
   * Adds an equality t1 = t2 to the database.
   */
  void addEquality(TNode t1, TNode t2, TNode reason);

  /**
   * Adds an dis-equality t1 != t2 to the database.
   */
  void addDisequality(TNode t1, TNode t2, TNode reason);

  /**
   * Returns the representative of the term t.
   */
  TNode getRepresentative(TNode t) const;

  /**
   * Returns true if the two nodes are in the same class.
   */
  bool areEqual(TNode t1, TNode t2) const;

  /**
   * Get an explanation of the equality t1 = t2. Returns the asserted equalities that
   * imply t1 = t2. Returns TNodes as the assertion equalities should be hashed somewhere
   * else. 
   */
  void explainEquality(TNode t1, TNode t2, std::vector<TNode>& equalities) const;

  /**
   * Get an explanation of the equality t1 = t2. Returns the asserted equalities that
   * imply t1 = t2. Returns TNodes as the assertion equalities should be hashed somewhere
   * else. 
   */
  void explainDisequality(TNode t1, TNode t2, std::vector<TNode>& equalities) const;

  /**
   * Add term to the trigger terms. The notify class will get notified when two 
   * trigger terms become equal. Thihs will only happen on trigger term 
   * representatives.
   */
  void addTriggerTerm(TNode t);

  /**
   * Returns true if t is a trigger term or equal to some other trigger term.
   */
  bool isTriggerTerm(TNode t) const;

  /**
   * Adds a notify trigger for equality t1 = t2, i.e. when t1 = t2 the notify will be called with
   * trigger.
   */
  void addTriggerEquality(TNode t1, TNode t2, TNode trigger);

  /**
   * Adds a notify trigger for dis-equality t1 != t2, i.e. when t1 != t2 the notify will be called with
   * trigger.
   */
  void addTriggerDisequality(TNode t1, TNode t2, TNode trigger);

  /**
   * Check whether the two terms are equal.
   */
  bool areEqual(TNode t1, TNode t2);

  /**
   * Check whether the two term are dis-equal.
   */
  bool areDisequal(TNode t1, TNode t2);
};

} // Namespace uf
} // Namespace theory
} // Namespace CVC4

