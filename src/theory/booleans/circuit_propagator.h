/*********************                                                        */
/*! \file circuit_propagator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A non-clausal circuit propagator for Boolean simplification
 **
 ** A non-clausal circuit propagator for Boolean simplification.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_H
#define CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_H

#include <functional>
#include <memory>
#include <unordered_map>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/lazy_proof_chain.h"
#include "expr/node.h"
#include "expr/proof_generator.h"
#include "expr/proof_node.h"
#include "theory/eager_proof_generator.h"
#include "theory/theory.h"
#include "theory/trust_node.h"
#include "util/hash.h"

namespace CVC4 {
namespace theory {
namespace booleans {

/**
 * The main purpose of the CircuitPropagator class is to maintain the
 * state of the circuit for subsequent calls to propagate(), so that
 * the same fact is not output twice, so that the same edge in the
 * circuit isn't propagated twice, etc.
 */
class CircuitPropagator
{
 public:
  /**
   * Value of a particular node
   */
  enum AssignmentStatus
  {
    /** Node is currently unassigned */
    UNASSIGNED = 0,
    /** Node is assigned to true */
    ASSIGNED_TO_TRUE,
    /** Node is assigned to false */
    ASSIGNED_TO_FALSE,
  };

  typedef std::unordered_map<Node, std::vector<Node>, NodeHashFunction>
      BackEdgesMap;

  /**
   * Construct a new CircuitPropagator.
   */
  CircuitPropagator(bool enableForward = true, bool enableBackward = true);

  /** Get Node assignment in circuit.  Assert-fails if Node is unassigned. */
  bool getAssignment(TNode n) const
  {
    AssignmentMap::iterator i = d_state.find(n);
    Assert(i != d_state.end() && (*i).second != UNASSIGNED);
    return (*i).second == ASSIGNED_TO_TRUE;
  }

  // Use custom context to ensure propagator is reset after use
  void initialize() { d_context.push(); }

  void setNeedsFinish(bool value) { d_needsFinish = value; }

  bool getNeedsFinish() { return d_needsFinish; }

  std::vector<TrustNode>& getLearnedLiterals() { return d_learnedLiterals; }

  /** Finish the computation and pop the internal context */
  void finish();

  /** Assert for propagation */
  void assertTrue(TNode assertion);

  /**
   * Propagate through the asserted circuit propagator. New information
   * discovered by the propagator are put in the substitutions vector used in
   * construction.
   *
   * @return a trust node encapsulating the proof for a conflict as a lemma that
   * proves false, or the null trust node otherwise
   */
  TrustNode propagate() CVC4_WARN_UNUSED_RESULT;

  /**
   * Get the back edges of this circuit.
   */
  const BackEdgesMap& getBackEdges() const { return d_backEdges; }

  /** Invert a set value */
  static inline AssignmentStatus neg(AssignmentStatus value)
  {
    Assert(value != UNASSIGNED);
    if (value == ASSIGNED_TO_TRUE)
      return ASSIGNED_TO_FALSE;
    else
      return ASSIGNED_TO_TRUE;
  }

  /** True iff Node is assigned in circuit (either true or false). */
  bool isAssigned(TNode n) const
  {
    AssignmentMap::const_iterator i = d_state.find(n);
    return i != d_state.end() && ((*i).second != UNASSIGNED);
  }

  /** True iff Node is assigned to the value. */
  bool isAssignedTo(TNode n, bool value) const
  {
    AssignmentMap::const_iterator i = d_state.find(n);
    if (i == d_state.end()) return false;
    if (value && ((*i).second == ASSIGNED_TO_TRUE)) return true;
    if (!value && ((*i).second == ASSIGNED_TO_FALSE)) return true;
    return false;
  }
  /**
   * Set proof node manager, context and parent proof generator.
   *
   * If parent is non-null, then it is responsible for the proofs provided
   * to this class.
   */
  void setProof(ProofNodeManager* pnm,
                context::Context* ctx,
                ProofGenerator* defParent);

 private:
  /** A context-notify object that clears out stale data. */
  template <class T>
  class DataClearer : context::ContextNotifyObj
  {
   public:
    DataClearer(context::Context* context, T& data)
        : context::ContextNotifyObj(context), d_data(data)
    {
    }

   protected:
    void contextNotifyPop() override
    {
      Trace("circuit-prop")
          << "CircuitPropagator::DataClearer: clearing data "
          << "(size was " << d_data.size() << ")" << std::endl;
      d_data.clear();
    }

   private:
    T& d_data;
  }; /* class DataClearer<T> */

  /** Predicate for use in STL functions. */
  class IsAssigned : public std::unary_function<TNode, bool>
  {
    CircuitPropagator& d_circuit;

   public:
    IsAssigned(CircuitPropagator& circuit) : d_circuit(circuit) {}

    bool operator()(TNode in) const { return d_circuit.isAssigned(in); }
  }; /* class IsAssigned */

  /** Predicate for use in STL functions. */
  class IsAssignedTo : public std::unary_function<TNode, bool>
  {
    CircuitPropagator& d_circuit;
    bool d_value;

   public:
    IsAssignedTo(CircuitPropagator& circuit, bool value)
        : d_circuit(circuit), d_value(value)
    {
    }

    bool operator()(TNode in) const
    {
      return d_circuit.isAssignedTo(in, d_value);
    }
  }; /* class IsAssignedTo */

  /**
   * Assignment status of each node.
   */
  typedef context::CDHashMap<TNode, AssignmentStatus, TNodeHashFunction>
      AssignmentMap;

  /**
   * Assign Node in circuit with the value and add it to the queue; note
   * conflicts.
   */
  void assignAndEnqueue(TNode n,
                        bool value,
                        std::shared_ptr<ProofNode> proof = nullptr);

  /**
   * Store a conflict for the case that we have derived both n and n.negate()
   * to be true.
   */
  void makeConflict(Node n);

  /**
   * Compute the map from nodes to the nodes that use it.
   */
  void computeBackEdges(TNode node);

  /**
   * Propagate new information forward in circuit to
   * the parents of "in".
   */
  void propagateForward(TNode child, bool assignment);

  /**
   * Propagate new information backward in circuit to
   * the children of "in".
   */
  void propagateBackward(TNode parent, bool assignment);

  /** Are proofs enabled? */
  bool isProofEnabled() const;

  context::Context d_context;

  /** The propagation queue */
  std::vector<TNode> d_propagationQueue;

  /**
   * We have a propagation queue "clearer" object for when the user
   * context pops.  Normally the propagation queue should be empty,
   * but this keeps us safe in case there's still some rubbish around
   * on the queue.
   */
  DataClearer<std::vector<TNode>> d_propagationQueueClearer;

  /** Are we in conflict? */
  context::CDO<TrustNode> d_conflict;

  /** Map of substitutions */
  std::vector<TrustNode> d_learnedLiterals;

  /**
   * Similar data clearer for learned literals.
   */
  DataClearer<std::vector<TrustNode>> d_learnedLiteralClearer;

  /**
   * Back edges from nodes to where they are used.
   */
  BackEdgesMap d_backEdges;

  /**
   * Similar data clearer for back edges.
   */
  DataClearer<BackEdgesMap> d_backEdgesClearer;

  /** Nodes that have been attached already (computed forward edges for) */
  // All the nodes we've visited so far
  context::CDHashSet<Node, NodeHashFunction> d_seen;

  AssignmentMap d_state;

  /** Whether to perform forward propagation */
  const bool d_forwardPropagation;

  /** Whether to perform backward propagation */
  const bool d_backwardPropagation;

  /* Does the current state require a call to finish()? */
  bool d_needsFinish;

  /** Adds a new proof for f, or drops it if we already have a proof */
  void addProof(TNode f, std::shared_ptr<ProofNode> pf);

  /** A pointer to the proof manager */
  ProofNodeManager* d_pnm;
  /** Eager proof generator that actually stores the proofs */
  std::unique_ptr<EagerProofGenerator> d_epg;
  /** Connects the proofs to subproofs internally */
  std::unique_ptr<LazyCDProofChain> d_proofInternal;
  /** Connects the proofs to assumptions externally */
  std::unique_ptr<LazyCDProofChain> d_proofExternal;
}; /* class CircuitPropagator */

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_H */
