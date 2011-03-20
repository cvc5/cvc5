/*********************                                                        */
/*! \file equality_engine.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#include <vector>
#include <ext/hash_map>

#include "expr/node.h"
#include "context/cdo.h"
#include "util/output.h"
#include "util/stats.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace bv {

struct BitSizeTraits {
  /** The null id */
  static const size_t id_null; // Defined in the cpp file (GCC bug)
  /** The null trigger id */
  static const size_t trigger_id_null;

  /** Number of bits we use for the id */
  static const size_t id_bits   = 24;
  /** Number of bits we use for the size the equivalence class */
  static const size_t size_bits = 16;
  /** Number of bits we use for the trigger id */
  static const size_t trigger_id_bits = 24;
};

class EqualityNode {

public:

  /** The size of this equivalence class (if it's a representative) */
  size_t d_size   : BitSizeTraits::size_bits;

  /** The id (in the eq-manager) of the representative equality node */
  size_t d_findId : BitSizeTraits::id_bits;

  /** The next equality node in this class */
  size_t d_nextId : BitSizeTraits::id_bits;

public:

  /**
   * Creates a new node, which is in a list of it's own.
   */
  EqualityNode(size_t nodeId = BitSizeTraits::id_null)
  : d_size(1), d_findId(nodeId), d_nextId(nodeId) {}

  /** Initialize the equality node */
  inline void init(size_t nodeId) {
    d_size = 1;
    d_findId = d_nextId = nodeId;
  }

  /**
   * Returns the next node in the class circular list.
   */
  inline size_t getNext() const {
    return d_nextId;
  }

  /**
   * Returns the size of this equivalence class (only valid if this is the representative).
   */
  inline size_t getSize() const {
    return d_size;
  }

  /**
   * Merges the two lists. If add size is true the size of this node is increased by the size of
   * the other node, otherwise the size is decreased by the size of the other node.
   */
  template<bool addSize>
  inline void merge(EqualityNode& other) {
    size_t tmp = d_nextId; d_nextId = other.d_nextId; other.d_nextId = tmp;
    if (addSize) {
      d_size += other.d_size;
    } else {
      d_size -= other.d_size;
    }
  }

  /**
   * Returns the class representative.
   */
  inline size_t getFind() const { return d_findId; }

  /**
   * Set the class representative.
   */
  inline void setFind(size_t findId) { d_findId = findId; }
};

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
class EqualityEngine {

public:

  /** Statistics about the equality engine instance */
  struct Statistics {
    /** Total number of merges */
    IntStat mergesCount;
    /** Number of terms managed by the system */
    IntStat termsCount;
    /** Number of function terms managed by the system */
    IntStat functionTermsCount;
    /** Number of times we performed a backtrack */
    IntStat backtracksCount;

    Statistics(std::string name)
    : mergesCount(name + "::mergesCount", 0),
      termsCount(name + "::termsCount", 0),
      functionTermsCount(name + "functionTermsCoutn", 0),
      backtracksCount(name + "::backtracksCount", 0)
    {
      StatisticsRegistry::registerStat(&mergesCount);
      StatisticsRegistry::registerStat(&termsCount);
      StatisticsRegistry::registerStat(&functionTermsCount);
      StatisticsRegistry::registerStat(&backtracksCount);
    }

    ~Statistics() {
      StatisticsRegistry::unregisterStat(&mergesCount);
      StatisticsRegistry::unregisterStat(&termsCount);
      StatisticsRegistry::unregisterStat(&functionTermsCount);
      StatisticsRegistry::unregisterStat(&backtracksCount);
    }
  };

private:

  /** The class to notify when a representative changes for a term */
  NotifyClass d_notify;

  /** Map from nodes to their ids */
  __gnu_cxx::hash_map<TNode, size_t, TNodeHashFunction> d_nodeIds;

  /** Map from ids to the nodes */
  std::vector<Node> d_nodes;

  /** Map from ids to the equality nodes */
  std::vector<EqualityNode> d_equalityNodes;

  /** Number of asserted equalities we have so far */
  context::CDO<size_t> d_assertedEqualitiesCount;

  /**
   * We keep a list of asserted equalities. Not among original terms, but
   * among the class representatives.
   */
  struct Equality {
    /** Left hand side of the equality */
    size_t lhs : BitSizeTraits::id_bits;
    /** Right hand side of the equality */
    size_t rhs : BitSizeTraits::id_bits;
    /** Equality constructor */
    Equality(size_t lhs = BitSizeTraits::id_null, size_t rhs = BitSizeTraits::id_null)
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
    size_t d_nodeId : BitSizeTraits::id_bits;
    // The next edge
    size_t d_nextId : BitSizeTraits::id_bits;

  public:

    EqualityEdge(size_t nodeId = BitSizeTraits::id_null, size_t nextId = BitSizeTraits::id_null)
    : d_nodeId(nodeId), d_nextId(nextId) {}

    /** Returns the id of the next edge */
    inline size_t getNext() const { return d_nextId; }

    /** Returns the id of the target edge node */
    inline size_t getNodeId() const { return d_nodeId; }
  };

  /**
   * All the equality edges (twice as many as the number of asserted equalities. If an equality
   * t1 = t2 is asserted, the edges added are -> t2, -> t1 (in this order). Hance, having the index
   * of one of the edges you can reconstruct the original equality.
   */
  std::vector<EqualityEdge> d_equalityEdges;

  /**
   * Reasons for equalities.
   */
  std::vector<Node> d_equalityReasons;

  /**
   * Map from a node to it's first edge in the equality graph. Edges are added to the front of the
   * list which makes the insertion/backtracking easy.
   */
  std::vector<size_t> d_equalityGraph;

  /** Add an edge to the equality graph */
  inline void addGraphEdge(size_t t1, size_t t2, Node reason);

  /** Returns the equality node of the given node */
  inline EqualityNode& getEqualityNode(TNode node);

  /** Returns the equality node of the given node */
  inline EqualityNode& getEqualityNode(size_t nodeId);

  /** Returns the id of the node */
  inline size_t getNodeId(TNode node) const;

  /** Merge the class2 into class1 */
  void merge(EqualityNode& class1, EqualityNode& class2, std::vector<size_t>& triggers);

  /** Undo the mereg of class2 into class1 */
  void undoMerge(EqualityNode& class1, EqualityNode& class2, size_t class2Id);

  /** Backtrack the information if necessary */
  void backtrack();

  /**
   * Data used in the BFS search through the equality graph.
   */
  struct BfsData {
    // The current node
    size_t nodeId : BitSizeTraits::id_bits;
    // The index of the edge we traversed
    size_t edgeId : BitSizeTraits::id_bits;
    // Index in the queue of the previous node. Shouldn't be too much of them, at most the size
    // of the biggest equivalence class
    size_t previousIndex : BitSizeTraits::size_bits;

    BfsData(size_t nodeId = BitSizeTraits::id_null, size_t edgeId = BitSizeTraits::id_null, size_t prev = 0)
    : nodeId(nodeId), edgeId(edgeId), previousIndex(prev) {}
  };

  /**
   * Trigger that will be updated
   */
  struct Trigger {
    /** The current class id of the LHS of the trigger */
    size_t classId : BitSizeTraits::id_bits;
    /** Next trigger for class 1 */
    size_t nextTrigger : BitSizeTraits::id_bits;

    Trigger(size_t classId, size_t nextTrigger)
    : classId(classId), nextTrigger(nextTrigger) {}
  };

  /**
   * Vector of triggers (persistent and not-backtrackable). Triggers come in pairs for an
   * equality trigger (t1, t2): one at position 2k for t1, and one at position 2k + 1 for t2. When
   * updating triggers we always know where the other one is (^1).
   */
  std::vector<Trigger> d_equalityTriggers;

  /**
   * Trigger lists per node. The begin id changes as we merge, but the end always points to
   * the actual end of the triggers for this node.
   */
  std::vector<size_t> d_nodeTriggers;

  /**
   * Adds the trigger with triggerId to the beginning of the trigger list of the node with id nodeId.
   */
  inline void addTriggerToList(size_t nodeId, size_t triggerId);

  /** Statistics */
  Statistics d_stats;

public:

  /**
   * Initialize the equality engine, given the owning class. This will initialize the notifier with
   * the owner information.
   */
  EqualityEngine(OwnerClass& owner, context::Context* context, std::string name)
  : d_notify(owner), d_assertedEqualitiesCount(context, 0), d_stats(name) {
    Debug("equality") << "EqualityEdge::EqualityEdge(): id_null = " << BitSizeTraits::id_null <<
        ", trigger_id_null = " << BitSizeTraits::trigger_id_null << std::endl;
  }

  /**
   * Adds a term to the term database. Returns the internal id of the term.
   */
  size_t addTerm(TNode t);

  /**
   * Check whether the node is already in the database.
   */
  inline bool hasTerm(TNode t) const;

  /**
   * Adds an equality t1 = t2 to the database. Returns false if any of the triggers failed.
   */
  bool addEquality(TNode t1, TNode t2, Node reason);

  /**
   * Returns the representative of the term t.
   */
  inline TNode getRepresentative(TNode t) const;

  /**
   * Returns true if the two nodes are in the same class.
   */
  inline bool areEqual(TNode t1, TNode t2) const;

  /**
   * Get an explanation of the equality t1 = t2. Returns the asserted equalities that
   * imply t1 = t2. Returns TNodes as the assertion equalities should be hashed somewhere
   * else. TODO: mark the phantom equalities (skolems).
   */
  void getExplanation(TNode t1, TNode t2, std::vector<TNode>& equalities) const;

  /**
   * Adds a notify trigger for equality t1 = t2, i.e. when t1 = t2 the notify will be called with
   * (t1, t2).
   */
  size_t addTrigger(TNode t1, TNode t2);

  /**
   * Normalizes a term by finding the representative. If the representative can be decomposed (using
   * UnionFindPreferences) it will try and recursively find the representatives, and substitute.
   * Assumptions used in normalization are retruned in the set.
   */
  Node normalize(TNode node, std::set<TNode>& assumptions);

private:

  /** Hash of normalizations to avioid cycles */
  typedef __gnu_cxx::hash_map<TNode, Node, TNodeHashFunction> normalization_cache;
  normalization_cache d_normalizationCache;

  /**
   * Same as above, but does cahcing to avoid loops.
   */
  Node normalizeWithCache(TNode node, std::set<TNode>& assumptions);

};

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
size_t EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::addTerm(TNode t) {

  Debug("equality") << "EqualityEngine::addTerm(" << t << ")" << std::endl;

  // If term already added, retrurn it's id
  if (hasTerm(t)) return getNodeId(t);

  ++ d_stats.termsCount;

  // Register the new id of the term
  size_t newId = d_nodes.size();
  d_nodeIds[t] = newId;
  // Add the node to it's position
  d_nodes.push_back(t);
  // Add the trigger list for this node
  d_nodeTriggers.push_back(BitSizeTraits::trigger_id_null);
  // Add it to the equality graph
  d_equalityGraph.push_back(BitSizeTraits::id_null);
  // Add the equality node to the nodes
  if (d_equalityNodes.size() <= newId) {
    d_equalityNodes.resize(newId + 100);
  }
  d_equalityNodes[newId].init(newId);
  // Return the id of the term
  return newId;
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
bool EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::hasTerm(TNode t) const {
  return d_nodeIds.find(t) != d_nodeIds.end();
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
size_t EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::getNodeId(TNode node) const {
  Assert(hasTerm(node), node.toString().c_str());
  return (*d_nodeIds.find(node)).second;
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
EqualityNode& EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::getEqualityNode(TNode t) {
  return getEqualityNode(getNodeId(t));
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
EqualityNode& EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::getEqualityNode(size_t nodeId) {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
bool EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::addEquality(TNode t1, TNode t2, Node reason) {

  Debug("equality") << "EqualityEngine::addEquality(" << t1 << "," << t2 << ")" << std::endl;

  // Backtrack if necessary
  backtrack();

  // Add the terms if they are not already in the database
  size_t t1Id = getNodeId(t1);
  size_t t2Id = getNodeId(t2);

  // Get the representatives
  size_t t1classId = getEqualityNode(t1Id).getFind();
  size_t t2classId = getEqualityNode(t2Id).getFind();

  // If already the same, we're done
  if (t1classId == t2classId) return true;

  // Get the nodes of the representatives
  EqualityNode& node1 = getEqualityNode(t1classId);
  EqualityNode& node2 = getEqualityNode(t2classId);

  Assert(node1.getFind() == t1classId);
  Assert(node2.getFind() == t2classId);

  // Depending on the merge preference (such as size), merge them
  std::vector<size_t> triggers;
  if (UnionFindPreferences::mergePreference(d_nodes[t2classId], node2.getSize(), d_nodes[t1classId], node1.getSize())) {
    Debug("equality") << "EqualityEngine::addEquality(" << t1 << "," << t2 << "): merging " << t1 << " into " << t2 << std::endl;
    merge(node2, node1, triggers);
    d_assertedEqualities.push_back(Equality(t2classId, t1classId));
  } else {
    Debug("equality") << "EqualityEngine::addEquality(" << t1 << "," << t2 << "): merging " << t2 << " into " << t1 << std::endl;
    merge(node1, node2, triggers);
    d_assertedEqualities.push_back(Equality(t1classId, t2classId));
  }

  // Add the actuall equality to the equality graph
  addGraphEdge(t1Id, t2Id, reason);

  // One more equality added
  d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;

  Assert(2*d_assertedEqualities.size() == d_equalityEdges.size());
  Assert(d_assertedEqualities.size() == d_assertedEqualitiesCount);

  // Notify the triggers
  for (size_t i = 0, i_end = triggers.size(); i < i_end; ++ i) {
    // Notify the trigger and exit if it fails
    if (!d_notify(triggers[i])) return false;
  }

  return true;
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
TNode EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::getRepresentative(TNode t) const {

  Debug("equality") << "EqualityEngine::getRepresentative(" << t << ")" << std::endl;

  Assert(hasTerm(t));

  // Both following commands are semantically const
  const_cast<EqualityEngine*>(this)->backtrack();
  size_t representativeId = const_cast<EqualityEngine*>(this)->getEqualityNode(t).getFind();

  Debug("equality") << "EqualityEngine::getRepresentative(" << t << ") => " << d_nodes[representativeId] << std::endl;

  return d_nodes[representativeId];
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
bool EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::areEqual(TNode t1, TNode t2) const {
  Debug("equality") << "EqualityEngine::areEqual(" << t1 << "," << t2 << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Both following commands are semantically const
  const_cast<EqualityEngine*>(this)->backtrack();
  size_t rep1 = const_cast<EqualityEngine*>(this)->getEqualityNode(t1).getFind();
  size_t rep2 = const_cast<EqualityEngine*>(this)->getEqualityNode(t2).getFind();

  Debug("equality") << "EqualityEngine::areEqual(" << t1 << "," << t2 << ") => " << (rep1 == rep2 ? "true" : "false") << std::endl;

  return rep1 == rep2;
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
void EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::merge(EqualityNode& class1, EqualityNode& class2, std::vector<size_t>& triggers) {

  Debug("equality") << "EqualityEngine::merge(" << class1.getFind() << "," << class2.getFind() << ")" << std::endl;

  Assert(triggers.empty());

  ++ d_stats.mergesCount;

  size_t class1Id = class1.getFind();
  size_t class2Id = class2.getFind();

  // Update class2 representative information
  size_t currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    currentNode.setFind(class1Id);

    // Go through the triggers and inform if necessary
    size_t currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != BitSizeTraits::trigger_id_null) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      Trigger& otherTrigger = d_equalityTriggers[currentTrigger ^ 1];

      // If the two are not already in the same class
      if (otherTrigger.classId != trigger.classId) {
        trigger.classId = class1Id;
        // If they became the same, call the trigger
        if (otherTrigger.classId == class1Id) {
          // Id of the real trigger is half the internal one
          triggers.push_back(currentTrigger >> 1);
        }
      }

      // Go to the next trigger
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Now merge the lists
  class1.merge<true>(class2);
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
void EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::undoMerge(EqualityNode& class1, EqualityNode& class2, size_t class2Id) {

  Debug("equality") << "EqualityEngine::undoMerge(" << class1.getFind() << "," << class2Id << ")" << std::endl;

  // Now unmerge the lists (same as merge)
  class1.merge<false>(class2);

  // Update class2 representative information
  size_t currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    currentNode.setFind(class2Id);

    // Go through the trigger list (if any) and undo the class
    size_t currentTrigger = d_nodeTriggers[currentId];
    while (currentTrigger != BitSizeTraits::trigger_id_null) {
      Trigger& trigger = d_equalityTriggers[currentTrigger];
      trigger.classId = class2Id;
      currentTrigger = trigger.nextTrigger;
    }

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
void EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::backtrack() {

  // If we need to backtrack then do it
  if (d_assertedEqualitiesCount < d_assertedEqualities.size()) {

    ++ d_stats.backtracksCount;

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
    d_equalityReasons.resize(d_assertedEqualitiesCount);
  }

}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
void EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::addGraphEdge(size_t t1, size_t t2, Node reason) {
  Debug("equality") << "EqualityEngine::addGraphEdge(" << d_nodes[t1] << "," << d_nodes[t2] << ")" << std::endl;
  size_t edge = d_equalityEdges.size();
  d_equalityEdges.push_back(EqualityEdge(t2, d_equalityGraph[t1]));
  d_equalityEdges.push_back(EqualityEdge(t1, d_equalityGraph[t2]));
  d_equalityGraph[t1] = edge;
  d_equalityGraph[t2] = edge | 1;
  d_equalityReasons.push_back(reason);
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
void EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::getExplanation(TNode t1, TNode t2, std::vector<TNode>& equalities) const {
  Assert(equalities.empty());
  Assert(t1 != t2);
  Assert(getRepresentative(t1) == getRepresentative(t2));

  Debug("equality") << "EqualityEngine::getExplanation(" << t1 << "," << t2 << ")" << std::endl;

  const_cast<EqualityEngine*>(this)->backtrack();

  // Queue for the BFS containing nodes
  std::vector<BfsData> bfsQueue;

  // The id's of the nodes
  size_t t1Id = getNodeId(t1);
  size_t t2Id = getNodeId(t2);

  // Find a path from t1 to t2 in the graph (BFS)
  bfsQueue.push_back(BfsData(t1Id, BitSizeTraits::id_null, 0));
  size_t currentIndex = 0;
  while (true) {
    // There should always be a path, and every node can be visited only once (tree)
    Assert(currentIndex < bfsQueue.size());

    // The next node to visit
    BfsData& current = bfsQueue[currentIndex];
    size_t currentNode = current.nodeId;

    Debug("equality") << "EqualityEngine::getExplanation(): currentNode =  " << d_nodes[currentNode] << std::endl;

    // Go through the equality edges of this node
    size_t currentEdge = d_equalityGraph[currentNode];

    while (currentEdge != BitSizeTraits::id_null) {
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
            // Add the actual equality to the vector
            equalities.push_back(d_equalityReasons[currentEdge >> 1]);
            Debug("equality") << "EqualityEngine::getExplanation(): adding: " << d_equalityReasons[currentEdge >> 1] << std::endl;

            // Go to the previous
            currentEdge = bfsQueue[currentIndex].edgeId;
            currentIndex = bfsQueue[currentIndex].previousIndex;
        } while (currentEdge != BitSizeTraits::id_null);

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

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
size_t EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::addTrigger(TNode t1, TNode t2) {

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << "," << t2 << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Get the information about t1
  size_t t1Id = getNodeId(t1);
  size_t t1TriggerId = d_nodeTriggers[t1Id];
  size_t t1classId = getEqualityNode(t1Id).getFind();

  // Get the information about t2
  size_t t2Id = getNodeId(t2);
  size_t t2TriggerId = d_nodeTriggers[t2Id];
  size_t t2classId = getEqualityNode(t2Id).getFind();

  // Create the triggers
  size_t t1NewTriggerId = d_equalityTriggers.size();
  size_t t2NewTriggerId = t1NewTriggerId | 1;
  d_equalityTriggers.push_back(Trigger(t1classId, t1TriggerId));
  d_equalityTriggers.push_back(Trigger(t2classId, t2TriggerId));

  // Add the trigger to the trigger graph
  d_nodeTriggers[t1Id] = t1NewTriggerId;
  d_nodeTriggers[t2Id] = t2NewTriggerId;

  Debug("equality") << "EqualityEngine::addTrigger(" << t1 << "," << t2 << ") => " << t1NewTriggerId / 2 << std::endl;

  // Return the global id of the trigger
  return t1NewTriggerId / 2;
}

template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
Node EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::normalize(TNode node, std::set<TNode>& assumptions) {
  d_normalizationCache.clear();
  Node result = Rewriter::rewrite(normalizeWithCache(node, assumptions));
  d_normalizationCache.clear();
  return result;
}


template <typename OwnerClass, typename NotifyClass, typename UnionFindPreferences>
Node EqualityEngine<OwnerClass, NotifyClass, UnionFindPreferences>::normalizeWithCache(TNode node, std::set<TNode>& assumptions) {

  Debug("equality") << "EqualityEngine::normalize(" << node << ")" << push << std::endl;

  normalization_cache::iterator find = d_normalizationCache.find(node);
  if (find != d_normalizationCache.end()) {
    if (find->second.isNull()) {
      // We are in a cycle
      return node;
    } else {
      // Not in a cycle, return it
      return find->second;
    }
  } else {
    d_normalizationCache[node] = Node();
  }

  // Get the representative
  Node result = hasTerm(node) ? getRepresentative(node) : node;
  if (node != result) {
    std::vector<TNode> equalities;
    getExplanation(result, node, equalities);
    assumptions.insert(equalities.begin(), equalities.end());
  }

  // If asked, substitute the children with their representatives
  if (UnionFindPreferences::descend(result)) {
    // Make the builder for substitution
    NodeBuilder<> builder;
    builder << result.getKind();
    kind::MetaKind metaKind = result.getMetaKind();
    if (metaKind == kind::metakind::PARAMETERIZED) {
      builder << result.getOperator();
    }
    for (unsigned i = 0; i < result.getNumChildren(); ++ i) {
      builder << normalizeWithCache(result[i], assumptions);
    }
    result = builder;
  }

  Debug("equality") << "EqualityEngine::normalize(" << node << ") => " << result << pop << std::endl;

  // Cache the result for real now
  d_normalizationCache[node] = result;

  return result;
}

} // Namespace bv
} // Namespace theory
} // Namespace CVC4

