/*********************                                                        */
/*! \file circuit_propagator.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A non-clausal circuit propagator for Boolean simplification
 **
 ** A non-clausal circuit propagator for Boolean simplification.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_H
#define __CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_H

#include <vector>
#include <functional>

#include "theory/theory.h"
#include "context/context.h"
#include "util/hash.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace booleans {

/**
 * The main purpose of the CircuitPropagator class is to maintain the
 * state of the circuit for subsequent calls to propagate(), so that
 * the same fact is not output twice, so that the same edge in the
 * circuit isn't propagated twice, etc.
 */
class CircuitPropagator {
  const std::vector<TNode>& d_atoms;
  const std::hash_map<TNode, std::vector<TNode>, TNodeHashFunction>& d_backEdges;

  class ConflictException : Exception {
  public:
    ConflictException() : Exception("A conflict was found in the CircuitPropagator") {
    }
  };/* class ConflictException */

  enum {
    ASSIGNMENT_MASK = 1,
    IS_ASSIGNED_MASK = 2,
    IS_PROPAGATED_FORWARD_MASK = 4,
    IS_PROPAGATED_BACKWARD_MASK = 8
  };/* enum */

  /**
   * For each Node we care about, we have a 4-bit state:
   *   Bit 0 (ASSIGNMENT_MASK) is set to indicate the current assignment
   *   Bit 1 (IS_ASSIGNED_MASK) is set if a value is assigned
   *   Bit 2 (IS_PROPAGATED_FORWARD) is set to indicate it's been propagated forward
   *   Bit 2 (IS_PROPAGATED_BACKWARD) is set to indicate it's been propagated backward
   */
  std::hash_map<TNode, unsigned, TNodeHashFunction> d_state;

  /** Assign Node in circuit with the value and add it to the changed vector; note conflicts. */
  void assign(TNode n, bool b, std::vector<TNode>& changed) {
    if(n.getMetaKind() == kind::metakind::CONSTANT) {
      bool c = n.getConst<bool>();
      if(c != b) {
        Debug("circuit-prop") << "while assigning(" << b << "): " << n
                              << ", constant conflict" << std::endl;
        throw ConflictException();
      } else {
        Debug("circuit-prop") << "assigning(" << b << "): " << n
                              << ", nothing to do" << std::endl;
      }
      return;
    }
    unsigned& state = d_state[n];
    if((state & IS_ASSIGNED_MASK) != 0) {// if assigned already
      if(((state & ASSIGNMENT_MASK) != 0) != b) {// conflict
        Debug("circuit-prop") << "while assigning(" << b << "): " << n
                              << ", got conflicting assignment(" << assignment(n) << "): "
                              << n << std::endl;
        throw ConflictException();
      } else {
        Debug("circuit-prop") << "already assigned(" << b << "): " << n << std::endl;
      }
    } else {// if unassigned
      Debug("circuit-prop") << "assigning(" << b << "): " << n << std::endl;
      state |= IS_ASSIGNED_MASK | (b ? ASSIGNMENT_MASK : 0);
      changed.push_back(n);
    }
  }
  /** True iff Node is assigned in circuit (either true or false). */
  bool isAssigned(TNode n) {
    return (d_state[n] & IS_ASSIGNED_MASK) != 0;
  }
  /** True iff Node is assigned in circuit (either true or false). */
  bool isAssigned(TNode n) const {
    std::hash_map<TNode, unsigned, TNodeHashFunction>::const_iterator i = d_state.find(n);
    return i != d_state.end() && ((*i).second & IS_ASSIGNED_MASK) != 0;
  }
  /** True iff Node is assigned in circuit with the value given. */
  bool isAssignedTo(TNode n, bool b) {
    unsigned state = d_state[n];
    return (state & IS_ASSIGNED_MASK) &&
      (state & ASSIGNMENT_MASK) == (b ? ASSIGNMENT_MASK : 0);
  }
  /** True iff Node is assigned in circuit (either true or false). */
  bool isAssignedTo(TNode n, bool b) const {
    std::hash_map<TNode, unsigned, TNodeHashFunction>::const_iterator i = d_state.find(n);
    return i != d_state.end() &&
      ((*i).second & IS_ASSIGNED_MASK) &&
      ((*i).second & ASSIGNMENT_MASK) == (b ? ASSIGNMENT_MASK : 0);
  }
  /** Get Node assignment in circuit.  Assert-fails if Node is unassigned. */
  bool assignment(TNode n) {
    unsigned state = d_state[n];
    Assert((state & IS_ASSIGNED_MASK) != 0);
    return (state & ASSIGNMENT_MASK) != 0;
  }
  /** Has this node already been propagated forward? */
  bool isPropagatedForward(TNode n) {
    return (d_state[n] & IS_PROPAGATED_FORWARD_MASK) != 0;
  }
  /** Has this node already been propagated backward? */
  bool isPropagatedBackward(TNode n) {
    return (d_state[n] & IS_PROPAGATED_BACKWARD_MASK) != 0;
  }
  /** Mark this node as already having been propagated forward. */
  void setPropagatedForward(TNode n) {
    d_state[n] |= IS_PROPAGATED_FORWARD_MASK;
  }
  /** Mark this node as already having been propagated backward. */
  void setPropagatedBackward(TNode n) {
    d_state[n] |= IS_PROPAGATED_BACKWARD_MASK;
  }

  /** Predicate for use in STL functions. */
  class IsAssigned : public std::unary_function<TNode, bool> {
    CircuitPropagator& d_circuit;
  public:
    IsAssigned(CircuitPropagator& circuit) :
      d_circuit(circuit) {
    }

    bool operator()(TNode in) const {
      return d_circuit.isAssigned(in);
    }
  };/* class IsAssigned */

  /** Predicate for use in STL functions. */
  class IsAssignedTo : public std::unary_function<TNode, bool> {
    CircuitPropagator& d_circuit;
    bool d_value;
  public:
    IsAssignedTo(CircuitPropagator& circuit, bool value) :
      d_circuit(circuit),
      d_value(value) {
    }

    bool operator()(TNode in) const {
      return d_circuit.isAssignedTo(in, d_value);
    }
  };/* class IsAssignedTo */

  /**
   * Propagate new information (in = polarity) forward in circuit to
   * the parents of "in".
   */
  void propagateForward(TNode in, bool polarity, std::vector<TNode>& newFacts);
  /**
   * Propagate new information (in = polarity) backward in circuit to
   * the children of "in".
   */
  void propagateBackward(TNode in, bool polarity, std::vector<TNode>& newFacts);

public:
  /**
   * Construct a new CircuitPropagator with the given atoms and backEdges.
   */
  CircuitPropagator(const std::vector<TNode>& atoms, const std::hash_map<TNode, std::vector<TNode>, TNodeHashFunction>& backEdges)
    : d_atoms(atoms),
      d_backEdges(backEdges) {
  }

  /**
   * Propagate new information (in == polarity) through the circuit
   * propagator.  New information discovered by the propagator are put
   * in the (output-only) newFacts vector.
   *
   * @return true iff conflict found
   */
  bool propagate(TNode in, bool polarity, std::vector<Node>& newFacts) CVC4_WARN_UNUSED_RESULT;

};/* class CircuitPropagator */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__CIRCUIT_PROPAGATOR_H */
