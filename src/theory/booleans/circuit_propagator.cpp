/*********************                                                        */
/*! \file circuit_propagator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A non-clausal circuit propagator for Boolean simplification
 **
 ** A non-clausal circuit propagator for Boolean simplification.
 **/

#include "theory/booleans/circuit_propagator.h"

#include <stack>
#include <vector>
#include <algorithm>

#include "expr/node_algorithm.h"
#include "util/utility.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace booleans {

void CircuitPropagator::assertTrue(TNode assertion)
{
  if (assertion.getKind() == kind::AND) {
    for (unsigned i = 0; i < assertion.getNumChildren(); ++ i) {
      assertTrue(assertion[i]);
    }
  } else {
    // Analyze the assertion for back-edges and all that
    computeBackEdges(assertion);
    // Assign the given assertion to true
    assignAndEnqueue(assertion, true);
  }
}

void CircuitPropagator::computeBackEdges(TNode node) {

  Debug("circuit-prop") << "CircuitPropagator::computeBackEdges(" << node << ")" << endl;

  // Vector of nodes to visit
  vector<TNode> toVisit;

  // Start with the top node
  if (d_seen.find(node) == d_seen.end()) {
    toVisit.push_back(node);
    d_seen.insert(node);
  }

  // Initialize the back-edges for the root, so we don't have a special case
  d_backEdges[node];

  // Go through the visit list
  for (unsigned i = 0; i < toVisit.size(); ++ i) {
    // Node we need to visit
    TNode current = toVisit[i];
    Debug("circuit-prop") << "CircuitPropagator::computeBackEdges(): processing " << current << endl;
    Assert(d_seen.find(current) != d_seen.end());

    // If this not an atom visit all the children and compute the back edges
    if (Theory::theoryOf(current) == THEORY_BOOL) {
      for (unsigned child = 0, child_end = current.getNumChildren(); child < child_end; ++ child) {
        TNode childNode = current[child];
        // Add the back edge
        d_backEdges[childNode].push_back(current);
        // Add to the queue if not seen yet
        if (d_seen.find(childNode) == d_seen.end()) {
          toVisit.push_back(childNode);
          d_seen.insert(childNode);
        }
      }
    }
  }
}

void CircuitPropagator::propagateBackward(TNode parent, bool parentAssignment) {

  Debug("circuit-prop") << "CircuitPropagator::propagateBackward(" << parent << ", " << parentAssignment << ")" << endl;

  // backward rules
  switch(parent.getKind()) {
  case kind::AND:
    if (parentAssignment) {
      // AND = TRUE: forall children c, assign(c = TRUE)
      for(TNode::iterator i = parent.begin(), i_end = parent.end(); i != i_end; ++i) {
        assignAndEnqueue(*i, true);
      }
    } else {
      // AND = FALSE: if all children BUT ONE == TRUE, assign(c = FALSE)
      TNode::iterator holdout = find_if_unique(parent.begin(), parent.end(), not1(IsAssignedTo(*this, true)));
      if (holdout != parent.end()) {
        assignAndEnqueue(*holdout, false);
      }
    }
    break;
  case kind::OR:
    if (parentAssignment) {
      // OR = TRUE: if all children BUT ONE == FALSE, assign(c = TRUE)
      TNode::iterator holdout = find_if_unique(parent.begin(), parent.end(), not1(IsAssignedTo(*this, false)));
      if (holdout != parent.end()) {
        assignAndEnqueue(*holdout, true);
      }
    } else {
      // OR = FALSE: forall children c, assign(c = FALSE)
      for(TNode::iterator i = parent.begin(), i_end = parent.end(); i != i_end; ++i) {
        assignAndEnqueue(*i, false);
      }
    }
    break;
  case kind::NOT:
    // NOT = b: assign(c = !b)
    assignAndEnqueue(parent[0], !parentAssignment);
    break;
  case kind::ITE:
    if (isAssignedTo(parent[0], true)) {
      // ITE c x y = v: if c is assigned and TRUE, assign(x = v)
      assignAndEnqueue(parent[1], parentAssignment);
    } else if (isAssignedTo(parent[0], false)) {
      // ITE c x y = v: if c is assigned and FALSE, assign(y = v)
      assignAndEnqueue(parent[2], parentAssignment);
    } else if (isAssigned(parent[1]) && isAssigned(parent[2])) {
      if (getAssignment(parent[1]) == parentAssignment && getAssignment(parent[2]) != parentAssignment) {
        // ITE c x y = v: if c is unassigned, x and y are assigned, x==v and y!=v, assign(c = TRUE)
        assignAndEnqueue(parent[0], true);
      } else if (getAssignment(parent[1]) != parentAssignment && getAssignment(parent[2]) == parentAssignment) {
        // ITE c x y = v: if c is unassigned, x and y are assigned, x!=v and y==v, assign(c = FALSE)
        assignAndEnqueue(parent[0], false);
      }
    }
    break;
  case kind::EQUAL:
    Assert(parent[0].getType().isBoolean());
    if (parentAssignment) {
      // IFF x y = TRUE: if x [resp y] is assigned, assign(y = x.assignment [resp x = y.assignment])
      if (isAssigned(parent[0])) {
        assignAndEnqueue(parent[1], getAssignment(parent[0]));
      } else if (isAssigned(parent[1])) {
        assignAndEnqueue(parent[0], getAssignment(parent[1]));
      }
    } else {
      // IFF x y = FALSE: if x [resp y] is assigned, assign(y = !x.assignment [resp x = !y.assignment])
      if (isAssigned(parent[0])) {
        assignAndEnqueue(parent[1], !getAssignment(parent[0]));
      } else if (isAssigned(parent[1])) {
        assignAndEnqueue(parent[0], !getAssignment(parent[1]));
      }
    }
    break;
  case kind::IMPLIES:
    if (parentAssignment) {
      if (isAssignedTo(parent[0], true)) {
        // IMPLIES x y = TRUE, and x == TRUE: assign(y = TRUE)
        assignAndEnqueue(parent[1], true);
      }
      if (isAssignedTo(parent[1], false)) {
        // IMPLIES x y = TRUE, and y == FALSE: assign(x = FALSE)
        assignAndEnqueue(parent[0], false);
      }
    } else {
      // IMPLIES x y = FALSE: assign(x = TRUE) and assign(y = FALSE)
      assignAndEnqueue(parent[0], true);
      assignAndEnqueue(parent[1], false);
    }
    break;
  case kind::XOR:
    if (parentAssignment) {
      if (isAssigned(parent[0])) {
        // XOR x y = TRUE, and x assigned, assign(y = !assignment(x))
        assignAndEnqueue(parent[1], !getAssignment(parent[0]));
      } else if (isAssigned(parent[1])) {
        // XOR x y = TRUE, and y assigned, assign(x = !assignment(y))
        assignAndEnqueue(parent[0], !getAssignment(parent[1]));
      }
    } else {
      if (isAssigned(parent[0])) {
        // XOR x y = FALSE, and x assigned, assign(y = assignment(x))
        assignAndEnqueue(parent[1], getAssignment(parent[0]));
      } else if (isAssigned(parent[1])) {
        // XOR x y = FALSE, and y assigned, assign(x = assignment(y))
        assignAndEnqueue(parent[0], getAssignment(parent[1]));
      }
    }
    break;
  default:
    Unhandled();
  }
}


void CircuitPropagator::propagateForward(TNode child, bool childAssignment) {

  // The assignment we have
  Debug("circuit-prop") << "CircuitPropagator::propagateForward(" << child << ", " << childAssignment << ")" << endl;

  // Get the back any nodes where this is child
  const vector<Node>& parents = d_backEdges.find(child)->second;

  // Go through the parents and see if there is anything to propagate
  vector<Node>::const_iterator parent_it = parents.begin();
  vector<Node>::const_iterator parent_it_end = parents.end();
  for(; parent_it != parent_it_end && !d_conflict; ++ parent_it) {
    // The current parent of the child
    TNode parent = *parent_it;
    Assert(expr::hasSubterm(parent, child));

    // Forward rules
    switch(parent.getKind()) {
    case kind::AND:
      if (childAssignment) {
        TNode::iterator holdout;
        holdout = find_if (parent.begin(), parent.end(), not1(IsAssignedTo(*this, true)));
        if (holdout == parent.end()) { // all children are assigned TRUE
          // AND ...(x=TRUE)...: if all children now assigned to TRUE, assign(AND = TRUE)
          assignAndEnqueue(parent, true);
        } else if (isAssignedTo(parent, false)) {// the AND is FALSE
          // is the holdout unique ?
          TNode::iterator other = find_if (holdout + 1, parent.end(), not1(IsAssignedTo(*this, true)));
          if (other == parent.end()) { // the holdout is unique
            // AND ...(x=TRUE)...: if all children BUT ONE now assigned to TRUE, and AND == FALSE, assign(last_holdout = FALSE)
            assignAndEnqueue(*holdout, false);
          }
        }
      } else {
        // AND ...(x=FALSE)...: assign(AND = FALSE)
        assignAndEnqueue(parent, false);
      }
      break;
    case kind::OR:
      if (childAssignment) {
        // OR ...(x=TRUE)...: assign(OR = TRUE)
        assignAndEnqueue(parent, true);
      } else {
        TNode::iterator holdout;
        holdout = find_if (parent.begin(), parent.end(), not1(IsAssignedTo(*this, false)));
        if (holdout == parent.end()) { // all children are assigned FALSE
          // OR ...(x=FALSE)...: if all children now assigned to FALSE, assign(OR = FALSE)
          assignAndEnqueue(parent, false);
        } else if (isAssignedTo(parent, true)) {// the OR is TRUE
          // is the holdout unique ?
          TNode::iterator other = find_if (holdout + 1, parent.end(), not1(IsAssignedTo(*this, false)));
          if (other == parent.end()) { // the holdout is unique
            // OR ...(x=FALSE)...: if all children BUT ONE now assigned to FALSE, and OR == TRUE, assign(last_holdout = TRUE)
            assignAndEnqueue(*holdout, true);
          }
        }
      }
      break;

    case kind::NOT:
      // NOT (x=b): assign(NOT = !b)
      assignAndEnqueue(parent, !childAssignment);
      break;

    case kind::ITE:
      if (child == parent[0]) {
        if (childAssignment) {
          if (isAssigned(parent[1])) {
            // ITE (c=TRUE) x y: if x is assigned, assign(ITE = x.assignment)
            assignAndEnqueue(parent, getAssignment(parent[1]));
          }
        } else {
          if (isAssigned(parent[2])) {
            // ITE (c=FALSE) x y: if y is assigned, assign(ITE = y.assignment)
            assignAndEnqueue(parent, getAssignment(parent[2]));
          }
        }
      }
      if (child == parent[1]) {
        if (isAssignedTo(parent[0], true)) {
          // ITE c (x=v) y: if c is assigned and TRUE, assign(ITE = v)
          assignAndEnqueue(parent, childAssignment);
        }
      }
      if (child == parent[2]) {
        Assert(child == parent[2]);
        if (isAssignedTo(parent[0], false)) {
          // ITE c x (y=v): if c is assigned and FALSE, assign(ITE = v)
          assignAndEnqueue(parent, childAssignment);
        }
      }
      break;
    case kind::EQUAL:
      Assert(parent[0].getType().isBoolean());
      if (isAssigned(parent[0]) && isAssigned(parent[1])) {
        // IFF x y: if x or y is assigned, assign(IFF = (x.assignment <=> y.assignment))
        assignAndEnqueue(parent, getAssignment(parent[0]) == getAssignment(parent[1]));
      } else {
        if (isAssigned(parent)) {
          if (child == parent[0]) {
            if (getAssignment(parent)) {
              // IFF (x = b) y: if IFF is assigned to TRUE, assign(y = b)
              assignAndEnqueue(parent[1], childAssignment);
            } else {
              // IFF (x = b) y: if IFF is assigned to FALSE, assign(y = !b)
              assignAndEnqueue(parent[1], !childAssignment);
            }
          } else {
            Assert(child == parent[1]);
            if (getAssignment(parent)) {
              // IFF x y = b: if IFF is assigned to TRUE, assign(x = b)
              assignAndEnqueue(parent[0], childAssignment);
            } else {
              // IFF x y = b y: if IFF is assigned to TRUE, assign(x = !b)
              assignAndEnqueue(parent[0], !childAssignment);
            }
          }
        }
      }
      break;
    case kind::IMPLIES:
      if (isAssigned(parent[0]) && isAssigned(parent[1])) {
        // IMPLIES (x=v1) (y=v2): assign(IMPLIES = (!v1 || v2))
        assignAndEnqueue(parent, !getAssignment(parent[0]) || getAssignment(parent[1]));
      } else {
        if (child == parent[0] && childAssignment && isAssignedTo(parent, true)) {
          // IMPLIES (x=TRUE) y [with IMPLIES == TRUE]: assign(y = TRUE)
          assignAndEnqueue(parent[1], true);
        }
        if (child == parent[1] && !childAssignment && isAssignedTo(parent, true)) {
          // IMPLIES x (y=FALSE) [with IMPLIES == TRUE]: assign(x = FALSE)
          assignAndEnqueue(parent[0], false);
        }
        // Note that IMPLIES == FALSE doesn't need any cases here
        // because if that assignment has been done, we've already
        // propagated all the children (in back-propagation).
      }
      break;
    case kind::XOR:
      if (isAssigned(parent)) {
        if (child == parent[0]) {
          // XOR (x=v) y [with XOR assigned], assign(y = (v ^ XOR)
          assignAndEnqueue(parent[1], childAssignment != getAssignment(parent));
        } else {
          Assert(child == parent[1]);
          // XOR x (y=v) [with XOR assigned], assign(x = (v ^ XOR))
          assignAndEnqueue(parent[0], childAssignment != getAssignment(parent));
        }
      }
      if (isAssigned(parent[0]) && isAssigned(parent[1])) {
        assignAndEnqueue(parent, getAssignment(parent[0]) != getAssignment(parent[1]));
      }
      break;
    default:
      Unhandled();
    }
  }
}

bool CircuitPropagator::propagate() {

  Debug("circuit-prop") << "CircuitPropagator::propagate()" << std::endl;

  for(unsigned i = 0; i < d_propagationQueue.size() && !d_conflict; ++ i) {

    // The current node we are propagating
    TNode current = d_propagationQueue[i];
    Debug("circuit-prop") << "CircuitPropagator::propagate(): processing " << current << std::endl;
    bool assignment = getAssignment(current);
    Debug("circuit-prop") << "CircuitPropagator::propagate(): assigned to " << (assignment ? "true" : "false") << std::endl;

    // Is this an atom
    bool atom = Theory::theoryOf(current) != THEORY_BOOL || current.isVar()
                || (current.getKind() == kind::EQUAL
                    && (current[0].isVar() && current[1].isVar()));

    // If an atom, add to the list for simplification
    if (atom) {
      Debug("circuit-prop") << "CircuitPropagator::propagate(): adding to learned: " << (assignment ? (Node)current : current.notNode()) << std::endl;
      d_learnedLiterals.push_back(assignment ? (Node)current : current.notNode());
    }

    // Propagate this value to the children (if not an atom or a constant)
    if (d_backwardPropagation && !atom && !current.isConst()) {
      propagateBackward(current, assignment);
    }
    // Propagate this value to the parents
    if (d_forwardPropagation) {
      propagateForward(current, assignment);
    }
  }

  // No conflict
  return d_conflict;
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
