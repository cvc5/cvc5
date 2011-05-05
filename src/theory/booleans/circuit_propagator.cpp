/*********************                                                        */
/*! \file circuit_propagator.cpp
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

#include "theory/booleans/circuit_propagator.h"
#include "util/utility.h"

#include <vector>
#include <algorithm>

using namespace std;

namespace CVC4 {
namespace theory {
namespace booleans {

void CircuitPropagator::propagateBackward(TNode in, bool polarity, vector<TNode>& changed) {
  if(!isPropagatedBackward(in)) {
    Debug("circuit-prop") << push << "propagateBackward(" << polarity << "): " << in << endl;
    setPropagatedBackward(in);
    // backward rules
    switch(Kind k = in.getKind()) {
    case kind::AND:
      if(polarity) {
        // AND = TRUE: forall children c, assign(c = TRUE)
        for(TNode::iterator i = in.begin(), i_end = in.end(); i != i_end; ++i) {
          Debug("circuit-prop") << "bAND1" << endl;
          assign(*i, true, changed);
        }
      } else {
        // AND = FALSE: if all children BUT ONE == TRUE, assign(c = FALSE)
        TNode::iterator holdout = find_if_unique(in.begin(), in.end(), not1(IsAssignedTo(*this, true)));
        if(holdout != in.end()) {
          Debug("circuit-prop") << "bAND2" << endl;
          assign(*holdout, false, changed);
        }
      }
      break;
    case kind::OR:
      if(polarity) {
        // OR = TRUE: if all children BUT ONE == FALSE, assign(c = TRUE)
        TNode::iterator holdout = find_if_unique(in.begin(), in.end(), not1(IsAssignedTo(*this, false)));
        if(holdout != in.end()) {
          Debug("circuit-prop") << "bOR1" << endl;
          assign(*holdout, true, changed);
        }
      } else {
        // OR = FALSE: forall children c, assign(c = FALSE)
        for(TNode::iterator i = in.begin(), i_end = in.end(); i != i_end; ++i) {
          Debug("circuit-prop") << "bOR2" << endl;
          assign(*i, false, changed);
        }
      }
      break;
    case kind::NOT:
      // NOT = b: assign(c = !b)
      Debug("circuit-prop") << "bNOT" << endl;
      assign(in[0], !polarity, changed);
      break;
    case kind::ITE:
      if(isAssignedTo(in[0], true)) {
        // ITE c x y = v: if c is assigned and TRUE, assign(x = v)
        Debug("circuit-prop") << "bITE1" << endl;
        assign(in[1], polarity, changed);
      } else if(isAssignedTo(in[0], false)) {
        // ITE c x y = v: if c is assigned and FALSE, assign(y = v)
        Debug("circuit-prop") << "bITE2" << endl;
        assign(in[2], polarity, changed);
      } else if(isAssigned(in[1]) && isAssigned(in[2])) {
        if(assignment(in[1]) == polarity && assignment(in[2]) != polarity) {
          // ITE c x y = v: if c is unassigned, x and y are assigned, x==v and y!=v, assign(c = TRUE)
          Debug("circuit-prop") << "bITE3" << endl;
          assign(in[0], true, changed);
        } else if(assignment(in[1]) == !polarity && assignment(in[2]) == polarity) {
          // ITE c x y = v: if c is unassigned, x and y are assigned, x!=v and y==v, assign(c = FALSE)
          Debug("circuit-prop") << "bITE4" << endl;
          assign(in[0], true, changed);
        }
      }
      break;
    case kind::IFF:
      if(polarity) {
        // IFF x y = TRUE: if x [resp y] is assigned, assign(y = x.assignment [resp x = y.assignment])
        if(isAssigned(in[0])) {
          assign(in[1], assignment(in[0]), changed);
          Debug("circuit-prop") << "bIFF1" << endl;
        } else if(isAssigned(in[1])) {
          Debug("circuit-prop") << "bIFF2" << endl;
          assign(in[0], assignment(in[1]), changed);
        }
      } else {
        // IFF x y = FALSE: if x [resp y] is assigned, assign(y = !x.assignment [resp x = !y.assignment])
        if(isAssigned(in[0])) {
          Debug("circuit-prop") << "bIFF3" << endl;
          assign(in[1], !assignment(in[0]), changed);
        } else if(isAssigned(in[1])) {
          Debug("circuit-prop") << "bIFF4" << endl;
          assign(in[0], !assignment(in[1]), changed);
        }
      }
      break;
    case kind::IMPLIES:
      if(polarity) {
        if(isAssignedTo(in[0], true)) {
          // IMPLIES x y = TRUE, and x == TRUE: assign(y = TRUE)
          Debug("circuit-prop") << "bIMPLIES1" << endl;
          assign(in[1], true, changed);
        }
        if(isAssignedTo(in[1], false)) {
          // IMPLIES x y = TRUE, and y == FALSE: assign(x = FALSE)
          Debug("circuit-prop") << "bIMPLIES2" << endl;
          assign(in[0], false, changed);
        }
      } else {
        // IMPLIES x y = FALSE: assign(x = TRUE) and assign(y = FALSE)
        Debug("circuit-prop") << "bIMPLIES3" << endl;
        assign(in[0], true, changed);
        assign(in[1], false, changed);
      }
      break;
    case kind::XOR:
      if(polarity) {
        if(isAssigned(in[0])) {
          // XOR x y = TRUE, and x assigned, assign(y = !assignment(x))
          Debug("circuit-prop") << "bXOR1" << endl;
          assign(in[1], !assignment(in[0]), changed);
        } else if(isAssigned(in[1])) {
          // XOR x y = TRUE, and y assigned, assign(x = !assignment(y))
          Debug("circuit-prop") << "bXOR2" << endl;
          assign(in[0], !assignment(in[1]), changed);
        }
      } else {
        if(isAssigned(in[0])) {
          // XOR x y = FALSE, and x assigned, assign(y = assignment(x))
          Debug("circuit-prop") << "bXOR3" << endl;
          assign(in[1], assignment(in[0]), changed);
        } else if(isAssigned(in[1])) {
          // XOR x y = FALSE, and y assigned, assign(x = assignment(y))
          Debug("circuit-prop") << "bXOR4" << endl;
          assign(in[0], assignment(in[1]), changed);
        }
      }
      break;
    case kind::CONST_BOOLEAN:
      // nothing to do
      break;
    default:
      Unhandled(k);
    }
    Debug("circuit-prop") << pop;
  }
}


void CircuitPropagator::propagateForward(TNode child, bool polarity, vector<TNode>& changed) {
  if(!isPropagatedForward(child)) {
    IndentedScope(Debug("circuit-prop"));
    Debug("circuit-prop") << "propagateForward (" << polarity << "): " << child << endl;
    std::hash_map<TNode, std::vector<TNode>, TNodeHashFunction>::const_iterator iter = d_backEdges.find(child);
    if(d_backEdges.find(child) == d_backEdges.end()) {
      Debug("circuit-prop") << "no backedges, must be ROOT?: " << child << endl;
      return;
    }
    const vector<TNode>& uses = (*iter).second;
    setPropagatedForward(child);
    for(vector<TNode>::const_iterator useIter = uses.begin(), useIter_end = uses.end(); useIter != useIter_end; ++useIter) {
      TNode in = *useIter; // this is the outer node
      Debug("circuit-prop") << "considering use: " << in << endl;
      IndentedScope(Debug("circuit-prop"));
      // forward rules
      switch(Kind k = in.getKind()) {
      case kind::AND:
        if(polarity) {
          TNode::iterator holdout;
          holdout = find_if(in.begin(), in.end(), not1(IsAssignedTo(*this, true)));
          if(holdout == in.end()) { // all children are assigned TRUE
            // AND ...(x=TRUE)...: if all children now assigned to TRUE, assign(AND = TRUE)
            Debug("circuit-prop") << "fAND1" << endl;
            assign(in, true, changed);
          } else if(isAssignedTo(in, false)) {// the AND is FALSE
            // is the holdout unique ?
            TNode::iterator other = find_if(holdout, in.end(), not1(IsAssignedTo(*this, true)));
            if(other == in.end()) { // the holdout is unique
              // AND ...(x=TRUE)...: if all children BUT ONE now assigned to TRUE, and AND == FALSE, assign(last_holdout = FALSE)
              Debug("circuit-prop") << "fAND2" << endl;
              assign(*holdout, false, changed);
            }
          }
        } else {
          // AND ...(x=FALSE)...: assign(AND = FALSE)
          Debug("circuit-prop") << "fAND3" << endl;
          assign(in, false, changed);
        }
        break;
      case kind::OR:
        if(polarity) {
          // OR ...(x=TRUE)...: assign(OR = TRUE)
          Debug("circuit-prop") << "fOR1" << endl;
          assign(in, true, changed);
        } else {
          TNode::iterator holdout;
          holdout = find_if(in.begin(), in.end(), not1(IsAssignedTo(*this, false)));
          if(holdout == in.end()) { // all children are assigned FALSE
            // OR ...(x=FALSE)...: if all children now assigned to FALSE, assign(OR = FALSE)
            Debug("circuit-prop") << "fOR2" << endl;
            assign(in, false, changed);
          } else if(isAssignedTo(in, true)) {// the OR is TRUE
            // is the holdout unique ?
            TNode::iterator other = find_if(holdout, in.end(), not1(IsAssignedTo(*this, false)));
            if(other == in.end()) { // the holdout is unique
              // OR ...(x=FALSE)...: if all children BUT ONE now assigned to FALSE, and OR == TRUE, assign(last_holdout = TRUE)
              Debug("circuit-prop") << "fOR3" << endl;
              assign(*holdout, true, changed);
            }
          }
        }
        break;

      case kind::NOT:
        // NOT (x=b): assign(NOT = !b)
        Debug("circuit-prop") << "fNOT" << endl;
        assign(in, !polarity, changed);
        break;
      case kind::ITE:
        if(child == in[0]) {
          if(polarity) {
            if(isAssigned(in[1])) {
              // ITE (c=TRUE) x y: if x is assigned, assign(ITE = x.assignment)
              Debug("circuit-prop") << "fITE1" << endl;
              assign(in, assignment(in[1]), changed);
            }
          } else {
            if(isAssigned(in[2])) {
              // ITE (c=FALSE) x y: if y is assigned, assign(ITE = y.assignment)
              Debug("circuit-prop") << "fITE2" << endl;
              assign(in, assignment(in[2]), changed);
            }
          }
        } else if(child == in[1]) {
          if(isAssignedTo(in[0], true)) {
            // ITE c (x=v) y: if c is assigned and TRUE, assign(ITE = v)
            Debug("circuit-prop") << "fITE3" << endl;
            assign(in, assignment(in[1]), changed);
          }
        } else {
          Assert(child == in[2]);
          if(isAssignedTo(in[0], false)) {
            // ITE c x (y=v): if c is assigned and FALSE, assign(ITE = v)
            Debug("circuit-prop") << "fITE4" << endl;
            assign(in, assignment(in[2]), changed);
          }
        }
        break;
      case kind::IFF:
        if(child == in[0]) {
          if(isAssigned(in[1])) {
            // IFF (x=b) y: if y is assigned, assign(IFF = (x.assignment <=> y.assignment))
            Debug("circuit-prop") << "fIFF1" << endl;
            assign(in, assignment(in[0]) == assignment(in[1]), changed);
          } else if(isAssigned(in)) {
            // IFF (x=b) y: if IFF is assigned, assign(y = (b <=> IFF.assignment))
            Debug("circuit-prop") << "fIFF2" << endl;
            assign(in[1], polarity == assignment(in), changed);
          }
        } else {
          Assert(child == in[1]);
          if(isAssigned(in[0])) {
            // IFF x (y=b): if x is assigned, assign(IFF = (x.assignment <=> y.assignment))
            Debug("circuit-prop") << "fIFF3" << endl;
            assign(in, assignment(in[0]) == assignment(in[1]), changed);
          } else if(isAssigned(in)) {
            // IFF x (y=b): if IFF is assigned, assign(x = (b <=> IFF.assignment))
            Debug("circuit-prop") << "fIFF4" << endl;
            assign(in[0], polarity == assignment(in), changed);
          }
        }
        break;
      case kind::IMPLIES:
        if(isAssigned(in[0]) && isAssigned(in[1])) {
          // IMPLIES (x=v1) (y=v2): assign(IMPLIES = (!v1 || v2))
          assign(in, !assignment(in[0]) || assignment(in[1]), changed);
          Debug("circuit-prop") << "fIMPLIES1" << endl;
        } else {
          if(child == in[0] && assignment(in[0]) && isAssignedTo(in, true)) {
            // IMPLIES (x=TRUE) y [with IMPLIES == TRUE]: assign(y = TRUE)
            Debug("circuit-prop") << "fIMPLIES2" << endl;
            assign(in[1], true, changed);
          }
          if(child == in[1] && !assignment(in[1]) && isAssignedTo(in, true)) {
            // IMPLIES x (y=FALSE) [with IMPLIES == TRUE]: assign(x = FALSE)
            Debug("circuit-prop") << "fIMPLIES3" << endl;
            assign(in[0], false, changed);
          }
          // Note that IMPLIES == FALSE doesn't need any cases here
          // because if that assignment has been done, we've already
          // propagated all the children (in back-propagation).
        }
        break;
      case kind::XOR:
        if(isAssigned(in)) {
          if(child == in[0]) {
            // XOR (x=v) y [with XOR assigned], assign(y = (v ^ XOR)
            Debug("circuit-prop") << "fXOR1" << endl;
            assign(in[1], polarity ^ assignment(in), changed);
          } else {
            Assert(child == in[1]);
            // XOR x (y=v) [with XOR assigned], assign(x = (v ^ XOR))
            Debug("circuit-prop") << "fXOR2" << endl;
            assign(in[0], polarity ^ assignment(in), changed);
          }
        }
        if( (child == in[0] && isAssigned(in[1])) ||
            (child == in[1] && isAssigned(in[0])) ) {
          // XOR (x=v) y [with y assigned], assign(XOR = (v ^ assignment(y))
          // XOR x (y=v) [with x assigned], assign(XOR = (assignment(x) ^ v)
          Debug("circuit-prop") << "fXOR3" << endl;
          assign(in, assignment(in[0]) ^ assignment(in[1]), changed);
        }
        break;
      case kind::CONST_BOOLEAN:
        InternalError("Forward-propagating a constant Boolean value makes no sense");
      default:
        Unhandled(k);
      }
    }
  }
}


bool CircuitPropagator::propagate(TNode in, bool polarity, vector<Node>& newFacts) {
  try {
    vector<TNode> changed;

    Assert(kindToTheoryId(in.getKind()) == THEORY_BOOL);

    Debug("circuit-prop") << "B: " << (polarity ? "" : "~") << in << endl;
    propagateBackward(in, polarity, changed);
    Debug("circuit-prop") << "F: " << (polarity ? "" : "~") << in << endl;
    propagateForward(in, polarity, changed);

    while(!changed.empty()) {
      vector<TNode> worklist;
      worklist.swap(changed);

      for(vector<TNode>::iterator i = worklist.begin(), i_end = worklist.end(); i != i_end; ++i) {
        if(kindToTheoryId((*i).getKind()) != THEORY_BOOL) {
          if(assignment(*i)) {
            newFacts.push_back(*i);
          } else {
            newFacts.push_back((*i).notNode());
          }
        } else {
          Debug("circuit-prop") << "B: " << (isAssignedTo(*i, true) ? "" : "~") << *i << endl;
          propagateBackward(*i, assignment(*i), changed);
          Debug("circuit-prop") << "F: " << (isAssignedTo(*i, true) ? "" : "~") << *i << endl;
          propagateForward(*i, assignment(*i), changed);
        }
      }
    }
  } catch(ConflictException& ce) {
    return true;
  }
  return false;
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
