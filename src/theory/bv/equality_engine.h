#include "cvc4_private.h"

#pragma once

#include <vector>
#include <ext/hash_map>

#include "expr/node.h"
#include "context/cdo.h"
#include "util/output.h"

namespace CVC4 {
namespace theory {
namespace bv {

struct NodeIdTraits {
  /** The null id */
  static const size_t null; // Defined in the cpp file (GCC bug)
  /** Number of bits we use for the id */
  static const size_t s_id_bits   = 24;
  /** Number of bits we use for the size the equivalence class */
  static const size_t s_size_bits = 16;
};

class EqualityNode {

public:

  /** The size of this equivalence class (if it's a representative) */
  size_t d_size   : NodeIdTraits::s_size_bits;

  /** The id (in the eq-manager) of the representative equality node */
  size_t d_findId : NodeIdTraits::s_id_bits;

  /** The next equality node in this class */
  size_t d_nextId : NodeIdTraits::s_id_bits;

public:

  /**
   * Creates a new node, which is in a list of it's own.
   */
  EqualityNode(size_t nodeId = NodeIdTraits::null)
  : d_size(1), d_findId(nodeId), d_nextId(nodeId) {}

  inline void init(size_t nodeId) {
    d_size = 1;
    d_findId = d_nextId = nodeId;
  }

  /**
   * Returns the next node in the class circural list.
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
      Assert(d_size + other.d_size > d_size);
      d_size += other.d_size;
    } else {
      Assert(d_size > other.d_size);
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


template <typename OwnerClass, typename NotifyClass>
class EqualityEngine {

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
    size_t lhs : NodeIdTraits::s_id_bits;
    /** Right hand side of the equality */
    size_t rhs : NodeIdTraits::s_id_bits;
    /** Equality constructor */
    Equality(size_t lhs = NodeIdTraits::null, size_t rhs = NodeIdTraits::null)
    : lhs(lhs), rhs(rhs) {}
  };

  /** The ids of the classes we have merged */
  std::vector<Equality> d_assertedEqualities;

  /**
   * An edge in the equality graph. This graph is an undirected graph (both edges added)
   * containing the actual asserted equalities.
   */
  class EqualityEdge {

    // The id of the RHS of this equality
    size_t d_nodeId : NodeIdTraits::s_id_bits;
    // The next edge
    size_t d_nextId : NodeIdTraits::s_id_bits;

  public:

    EqualityEdge(size_t nodeId = NodeIdTraits::null, size_t nextId = NodeIdTraits::null)
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
   * Map from a node to it's first edge in the equality graph. Edges are added to the front of the
   * list which makes the insertion/backtracking easy.
   */
  std::vector<size_t> d_equalityGraph;

  /** Add an edge to the equality graph */
  inline void addGraphEdge(size_t t1, size_t t2);

  /** Returns the equality node of the given node */
  inline EqualityNode& getEqualityNode(TNode node);

  /** Returns the equality node of the given node */
  inline EqualityNode& getEqualityNode(size_t nodeId);

  /** Returns the id of the node */
  inline size_t getNodeId(TNode node) const;

  /** Merge the class2 into class1 */
  void merge(EqualityNode& class1, EqualityNode& class2);

  /** Undo the mereg of class2 into class1 */
  void undoMerge(EqualityNode& class1, EqualityNode& class2, size_t class2Id);

  /** Backtrack the information if necessary */
  void backtrack();

  /**
   * Data used in the BFS search through the equality graph.
   */
  struct BfsData {
    // The current node
    size_t nodeId : NodeIdTraits::s_id_bits;
    // The index of the edge we traversed
    size_t edgeId : NodeIdTraits::s_id_bits;
    // Index in the queue of the previous node. Shouldn't be too much of them, at most the size
    // of the biggest equivalence class
    size_t previousIndex : NodeIdTraits::s_size_bits;

    BfsData(size_t nodeId = NodeIdTraits::null, size_t edgeId = NodeIdTraits::null, size_t prev = 0)
    : nodeId(nodeId), edgeId(edgeId), previousIndex(prev) {}
  };

  /**
   * Trigger that will
   */
  struct Trigger {
    size_t class1Id : NodeIdTraits::s_id_bits;
    size_t class2Id : NodeIdTraits::s_id_bits;
  };


public:

  /**
   * Initialize the equalty engine, given the owning class. This will initialize the notifier with
   * the owner information.
   */
  EqualityEngine(OwnerClass& owner, context::Context* context)
  : d_notify(owner), d_assertedEqualitiesCount(context, 0) {}

  /**
   * Adds a term to the term database. Returns the internal id of the term.
   */
  size_t addTerm(TNode t);

  /**
   * Check whether the node is already in the database.
   */
  inline bool hasTerm(TNode t) const;

  /**
   * Adds an equality t1 = t2 to the database.
   */
  void addEquality(TNode t1, TNode t2);

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
  void addTrigger(TNode t1, TNode t2);

};

template <typename OwnerClass, typename NotifyClass>
size_t EqualityEngine<OwnerClass, NotifyClass>::addTerm(TNode t) {

  Debug("equality") << "addTerm(" << t << ")" << std::endl;

  // If term already added, retrurn it's id
  if (hasTerm(t)) return getNodeId(t);

  // Register the new id of the term
  size_t newId = d_nodes.size();
  d_nodeIds[t] = newId;
  // Add the node to it's position
  d_nodes.push_back(t);
  // Add it to the equality graph
  d_equalityGraph.push_back(NodeIdTraits::null);
  // Add the equality node to the nodes
  if (d_equalityNodes.size() <= newId) {
    d_equalityNodes.resize(newId + 100);
  }
  d_equalityNodes[newId].init(newId);
  // Return the id of the term
  return newId;
}

template <typename OwnerClass, typename NotifyClass>
bool EqualityEngine<OwnerClass, NotifyClass>::hasTerm(TNode t) const {
  return d_nodeIds.find(t) != d_nodeIds.end();
}

template <typename OwnerClass, typename NotifyClass>
size_t EqualityEngine<OwnerClass, NotifyClass>::getNodeId(TNode node) const {
  Assert(hasTerm(node));
  return (*d_nodeIds.find(node)).second;
}

template <typename OwnerClass, typename NotifyClass>
EqualityNode& EqualityEngine<OwnerClass, NotifyClass>::getEqualityNode(TNode t) {
  return getEqualityNode(getNodeId(t));
}

template <typename OwnerClass, typename NotifyClass>
EqualityNode& EqualityEngine<OwnerClass, NotifyClass>::getEqualityNode(size_t nodeId) {
  Assert(nodeId < d_equalityNodes.size());
  return d_equalityNodes[nodeId];
}

template <typename OwnerClass, typename NotifyClass>
void EqualityEngine<OwnerClass, NotifyClass>::addEquality(TNode t1, TNode t2) {

  Debug("equality") << "addEquality(" << t1 << "," << t2 << ")" << std::endl;

  // Backtrack if necessary
  backtrack();

  // Add the terms if they are not already in the database
  size_t t1Id = getNodeId(t1);
  size_t t2Id = getNodeId(t2);

  // Get the representatives
  size_t t1classId = getEqualityNode(t1Id).getFind();
  size_t t2classId = getEqualityNode(t2Id).getFind();

  // If already the same, we're done
  if (t1classId == t2classId) return;

  // Get the nodes of the representatives
  EqualityNode& node1 = getEqualityNode(t1classId);
  EqualityNode& node2 = getEqualityNode(t2classId);

  Assert(node1.getFind() == t1classId);
  Assert(node2.getFind() == t2classId);

  // Depending on the size, merge them
  if (node1.getSize() < node2.getSize()) {
    merge(node2, node1);
    d_assertedEqualities.push_back(Equality(t2classId, t1classId));
  } else {
    merge(node1, node2);
    d_assertedEqualities.push_back(Equality(t1classId, t2classId));
  }

  // Add the actuall equality to the equality graph
  addGraphEdge(t1Id, t2Id);

  Assert(2*d_assertedEqualities.size() == d_equalityEdges.size());

  // One more equality added
  d_assertedEqualitiesCount = d_assertedEqualitiesCount + 1;
}

template <typename OwnerClass, typename NotifyClass>
TNode EqualityEngine<OwnerClass, NotifyClass>::getRepresentative(TNode t) const {

  Debug("equality") << "getRepresentative(" << t << ")" << std::endl;

  Assert(hasTerm(t));

  // Both following commands are semantically const
  const_cast<EqualityEngine*>(this)->backtrack();
  size_t representativeId = const_cast<EqualityEngine*>(this)->getEqualityNode(t).getFind();

  Debug("equality") << "getRepresentative(" << t << ") => " << d_nodes[representativeId] << std::endl;

  return d_nodes[representativeId];
}

template <typename OwnerClass, typename NotifyClass>
bool EqualityEngine<OwnerClass, NotifyClass>::areEqual(TNode t1, TNode t2) const {
  Debug("equality") << "areEqual(" << t1 << "," << t2 << ")" << std::endl;

  Assert(hasTerm(t1));
  Assert(hasTerm(t2));

  // Both following commands are semantically const
  const_cast<EqualityEngine*>(this)->backtrack();
  size_t rep1 = const_cast<EqualityEngine*>(this)->getEqualityNode(t1).getFind();
  size_t rep2 = const_cast<EqualityEngine*>(this)->getEqualityNode(t2).getFind();

  Debug("equality") << "areEqual(" << t1 << "," << t2 << ") => " << (rep1 == rep2 ? "true" : "false") << std::endl;

  return rep1 == rep2;
}

template <typename OwnerClass, typename NotifyClass>
void EqualityEngine<OwnerClass, NotifyClass>::merge(EqualityNode& class1, EqualityNode& class2) {

  Debug("equality") << "merge(" << class1.getFind() << "," << class2.getFind() << ")" << std::endl;

  size_t class1Id = class1.getFind();
  size_t class2Id = class2.getFind();

  // Update class2 representative information
  size_t currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    currentNode.setFind(class1Id);

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

  // Now merge the lists
  class1.merge<true>(class2);
}

template <typename OwnerClass, typename NotifyClass>
void EqualityEngine<OwnerClass, NotifyClass>::undoMerge(EqualityNode& class1, EqualityNode& class2, size_t class2Id) {

  Debug("equality") << "undoMerge(" << class1.getFind() << "," << class2Id << ")" << std::endl;

  // Now unmerge the lists (same as merge)
  class1.merge<false>(class2);

  // Update class2 representative information
  size_t currentId = class2Id;
  do {
    // Get the current node
    EqualityNode& currentNode = getEqualityNode(currentId);

    // Update it's find to class1 id
    currentNode.setFind(class2Id);

    // Move to the next node
    currentId = currentNode.getNext();

  } while (currentId != class2Id);

}

template <typename OwnerClass, typename NotifyClass>
void EqualityEngine<OwnerClass, NotifyClass>::backtrack() {

  // If we need to backtrack then do it
  if (d_assertedEqualitiesCount < d_assertedEqualities.size()) {

    Debug("equality") << "backtrack(): nodes" << std::endl;

    for (int i = (int)d_assertedEqualities.size() - 1, i_end = (int)d_assertedEqualitiesCount; i >= i_end; --i) {
      // Get the ids of the merged classes
      Equality& eq = d_assertedEqualities[i];
      // Undo the merge
      undoMerge(d_equalityNodes[eq.lhs], d_equalityNodes[eq.rhs], eq.rhs);
    }

    d_assertedEqualities.resize(d_assertedEqualitiesCount);

    Debug("equality") << "backtrack(): edges" << std::endl;

    for (int i = (int)d_equalityEdges.size() - 2, i_end = (int)(2*d_assertedEqualitiesCount); i >= i_end; i -= 2) {
      EqualityEdge& edge1 = d_equalityEdges[i];
      EqualityEdge& edge2 = d_equalityEdges[i | 1];
      d_equalityGraph[edge2.getNodeId()] = edge1.getNext();
      d_equalityGraph[edge1.getNodeId()] = edge2.getNext();
    }

    d_equalityEdges.resize(2 * d_assertedEqualitiesCount);
  }

}

template <typename OwnerClass, typename NotifyClass>
void EqualityEngine<OwnerClass, NotifyClass>::addGraphEdge(size_t t1, size_t t2) {
  size_t edge = d_equalityEdges.size();
  d_equalityEdges.push_back(EqualityEdge(t2, d_equalityGraph[t1]));
  d_equalityEdges.push_back(EqualityEdge(t1, d_equalityGraph[t2]));
  d_equalityGraph[t1] = edge;
  d_equalityGraph[t2] = edge | 1;
}

template <typename OwnerClass, typename NotifyClass>
void EqualityEngine<OwnerClass, NotifyClass>::getExplanation(TNode t1, TNode t2, std::vector<TNode>& equalities) const {
  Assert(equalities.empty());
  Assert(t1 != t2);
  Assert(getRepresentative(t1) == getRepresentative(t2));

  Debug("equality") << "getExplanation(" << t1 << "," << t2 << ")" << std::endl;

  const_cast<EqualityEngine*>(this)->backtrack();

  // Queue for the BFS containing nodes
  std::vector<BfsData> bfsQueue;

  // The id's of the nodes
  size_t t1Id = getNodeId(t1);
  size_t t2Id = getNodeId(t2);

  // Find a path from t1 to t2 in the graph (BFS)
  bfsQueue.push_back(BfsData(t1Id, NodeIdTraits::null, 0));
  size_t currentIndex = 0;
  while (true) {
    // There should always be a path, and every node can be visited only once (tree)
    Assert(currentIndex < bfsQueue.size());

    // The next node to visit
    BfsData& current = bfsQueue[currentIndex];
    size_t currentNode = current.nodeId;

    Debug("equality") << "getExplanation(): currentNode: " << currentNode << std::endl;

    // Go through the equality edges of this node
    size_t currentEdge = d_equalityGraph[currentNode];

    while (currentEdge != NodeIdTraits::null) {
      Debug("equality") << "getExplanation(): currentEdge: " << currentEdge << std::endl;

      // Get the edge
      const EqualityEdge& edge = d_equalityEdges[currentEdge];

      // Did we find the path
      if (edge.getNodeId() == t2Id) {

        Debug("equality") << "getExplanation(): path found: " << std::endl;

        // Reconstruct the path
        do {
          // Get the left and right hand side from the edge
          size_t firstEdge = (currentEdge >> 1) << 1;
          size_t secondEdge = (currentEdge | 1);
          TNode lhs = d_nodes[d_equalityEdges[secondEdge].getNodeId()];
          TNode rhs = d_nodes[d_equalityEdges[firstEdge].getNodeId()];
          // Add the actual equality to the vector
          equalities.push_back(lhs.eqNode(rhs));

          Debug("equality") << "getExplanation(): adding: " << lhs.eqNode(rhs) << std::endl;

          // Go to the previous
          currentEdge = bfsQueue[currentIndex].edgeId;
          currentIndex = bfsQueue[currentIndex].previousIndex;
        } while (currentEdge != NodeIdTraits::null);

        // Done
        return;
      }

      // Push to the visitation queue if it's not the backward edge 
      if ((currentEdge | 1) != (current.edgeId | 1)) {
        bfsQueue.push_back(BfsData(edge.getNodeId(), currentEdge, currentIndex));
      }
      
      // Go to the next edge
      currentEdge = edge.getNext();
    }

    // Go to the next node to visit
    ++ currentIndex;
  }
}

template <typename OwnerClass, typename NotifyClass>
void EqualityEngine<OwnerClass, NotifyClass>::addTrigger(TNode t1, TNode t2) {



}



} // Namespace bv
} // Namespace theory
} // Namespace CVC4

