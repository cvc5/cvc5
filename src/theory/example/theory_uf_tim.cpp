/*********************                                                        */
/*! \file theory_uf_tim.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the theory of uninterpreted functions.
 **
 ** Implementation of the theory of uninterpreted functions.
 **/

#include "theory/uf/tim/theory_uf_tim.h"
#include "theory/uf/tim/ecdata.h"
#include "expr/kind.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;
using namespace CVC4::theory::uf::tim;

TheoryUFTim::TheoryUFTim(Context* c, UserContext* u, OutputChannel& out, Valuation valuation) :
  Theory(THEORY_UF, c, u, out, valuation),
  d_assertions(c),
  d_pending(c),
  d_currentPendingIdx(c,0),
  d_disequality(c),
  d_registered(c) {
  Warning() << "NOTE:" << std::endl
            << "NOTE: currently the 'Tim' UF solver is broken," << std::endl
            << "NOTE: since its registerTerm() function is never" << std::endl
            << "NOTE: called." << std::endl
            << "NOTE:" << std::endl;
}

TheoryUFTim::~TheoryUFTim() {
}

void TheoryUFTim::preRegisterTerm(TNode n) {
  Debug("uf") << "uf: begin preRegisterTerm(" << n << ")" << std::endl;
  Debug("uf") << "uf: end preRegisterTerm(" << n << ")" << std::endl;
}

void TheoryUFTim::registerTerm(TNode n) {

  Debug("uf") << "uf: begin registerTerm(" << n << ")" << std::endl;

  d_registered.push_back(n);

  ECData* ecN;

  if(n.getAttribute(ECAttr(), ecN)) {
    /* registerTerm(n) is only called when a node has not been seen in the
     * current context.  ECAttr() is not a context-dependent attribute.
     * When n.hasAttribute(ECAttr(),...) is true on a registerTerm(n) call,
     * then it must be the case that this attribute was created in a previous
     * and no longer valid context. Because of this we have to reregister the
     * predecessors lists.
     * Also we do not have to worry about duplicates because all of the Link*
     * setup before are removed when the context n was setup in was popped out
     * of. All we are going to do here are sanity checks.
     */

    /*
     * Consider the following chain of events:
     * 1) registerTerm(n) is called on node n where n : f(m) in context level X,
     * 2) A new ECData is created on the heap, ecN,
     * 3) n is added to the predessecor list of m in context level X,
     * 4) We pop out of X,
     * 5) n is removed from the predessecor list of m because this is context
     *    dependent, the Link* will be destroyed and pointers to the Link
     *    structs in the ECData objects will be updated.
     * 6) registerTerm(n) is called on node n in context level Y,
     * 7) If n.hasAttribute(ECAttr(), &ecN), then ecN is still around,
     *    but the predecessor list is not
     *
     * The above assumes that the code is working correctly.
     */
    Assert(ecN->getFirst() == NULL)
        << "Equivalence class data exists for the node being registered.  "
           "Expected getFirst() == NULL.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking";
    /*Assert(ecN->getLast() == NULL,
           "Equivalence class data exists for the node being registered.  "
           "Expected getLast() == NULL.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking.");*/
    Assert(ecN->isClassRep())
        << "Equivalence class data exists for the node being registered.  "
           "Expected isClassRep() to be true.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking";
    Assert(ecN->getWatchListSize() == 0)
        << "Equivalence class data exists for the node being registered.  "
           "Expected getWatchListSize() == 0.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking";
  } else {
    //The attribute does not exist, so it is created and set
    ecN = new (true) ECData(getContext(), n);
    n.setAttribute(ECAttr(), ecN);
  }

  /* If the node is an APPLY_UF, we need to add it to the predecessor list
   * of its children.
   */
  if(n.getKind() == APPLY_UF) {
    TNode::iterator cIter = n.begin();

    for(; cIter != n.end(); ++cIter) {
      TNode child = *cIter;

      /* Because this can be called after nodes have been merged, we need
       * to lookup the representative in the UnionFind datastructure.
       */
      ECData* ecChild = ccFind(child.getAttribute(ECAttr()));

      /* Because this can be called after nodes have been merged we may need
       * to be merged with other predecessors of the equivalence class.
       */
      for(Link* Px = ecChild->getFirst(); Px != NULL; Px = Px->d_next ) {
        if(equiv(n, Px->d_data)) {
          Node pend = n.eqNode(Px->d_data);
          d_pending.push_back(pend);
        }
      }

      ecChild->addPredecessor(n);
    }
  }
  Debug("uf") << "uf: end registerTerm(" << n << ")" << std::endl;

}

bool TheoryUFTim::sameCongruenceClass(TNode x, TNode y) {
  return
    ccFind(x.getAttribute(ECAttr())) ==
    ccFind(y.getAttribute(ECAttr()));
}

bool TheoryUFTim::equiv(TNode x, TNode y) {
  Assert(x.getKind() == kind::APPLY_UF);
  Assert(y.getKind() == kind::APPLY_UF);

  if(x.getNumChildren() != y.getNumChildren()) {
    return false;
  }

  if(x.getOperator() != y.getOperator()) {
    return false;
  }

  // intentionally don't look at operator

  TNode::iterator xIter = x.begin();
  TNode::iterator yIter = y.begin();

  while(xIter != x.end()) {

    if(!sameCongruenceClass(*xIter, *yIter)) {
      return false;
    }

    ++xIter;
    ++yIter;
  }
  return true;
}

/* This is a very basic, but *obviously correct* find implementation
 * of the classic find algorithm.
 * TODO after we have done some more testing:
 * 1) Add path compression.  This is dependent on changes to ccUnion as
 *    many better algorithms use eager path compression.
 * 2) Elminate recursion.
 */
ECData* TheoryUFTim::ccFind(ECData * x) {
  if(x->getFind() == x) {
    return x;
  } else {
    return ccFind(x->getFind());
  }
  /* Slightly better Find w/ path compression and no recursion*/
  /*
    ECData* start;
    ECData* next = x;
    while(x != x->getFind()) x=x->getRep();
    while( (start = next) != x) {
      next = start->getFind();
      start->setFind(x);
    }
    return x;
  */
}

void TheoryUFTim::ccUnion(ECData* ecX, ECData* ecY) {
  ECData* nslave;
  ECData* nmaster;

  if(ecX->getWatchListSize() <= ecY->getWatchListSize()) {
    nslave = ecX;
    nmaster = ecY;
  } else {
    nslave = ecY;
    nmaster = ecX;
  }

  nslave->setFind(nmaster);

  for(Link* Px = nmaster->getFirst(); Px != NULL; Px = Px->d_next ) {
    for(Link* Py = nslave->getFirst(); Py != NULL; Py = Py->d_next ) {
      if(equiv(Px->d_data,Py->d_data)) {
        Node pendingEq = (Px->d_data).eqNode(Py->d_data);
        d_pending.push_back(pendingEq);
      }
    }
  }

  ECData::takeOverDescendantWatchList(nslave, nmaster);
}

void TheoryUFTim::merge() {
  while(d_currentPendingIdx < d_pending.size() ) {
    Node assertion = d_pending[d_currentPendingIdx];
    d_currentPendingIdx = d_currentPendingIdx + 1;

    TNode x = assertion[0];
    TNode y = assertion[1];

    ECData* tmpX = x.getAttribute(ECAttr());
    ECData* tmpY = y.getAttribute(ECAttr());

    ECData* ecX = ccFind(tmpX);
    ECData* ecY = ccFind(tmpY);
    if(ecX == ecY)
      continue;

    Debug("uf") << "merging equivalence classes for " << std::endl;
    Debug("uf") << "left equivalence class :" << (ecX->getRep()) << std::endl;
    Debug("uf") << "right equivalence class :" << (ecY->getRep()) << std::endl;
    Debug("uf") << std::endl;

    ccUnion(ecX, ecY);
  }
}

Node TheoryUFTim::constructConflict(TNode diseq) {
  Debug("uf") << "uf: begin constructConflict()" << std::endl;

  NodeBuilder<> nb(kind::AND);
  nb << diseq;
  for(unsigned i = 0; i < d_assertions.size(); ++i) {
    nb << d_assertions[i];
  }

  Assert(nb.getNumChildren() > 0);
  Node conflict = nb.getNumChildren() == 1 ? nb[0] : nb;

  Debug("uf") << "conflict constructed : " << conflict << std::endl;

  Debug("uf") << "uf: ending constructConflict()" << std::endl;

  return conflict;
}

void TheoryUFTim::check(Effort level) {
  if (done() && !fullEffort(level)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  Debug("uf") << "uf: begin check(" << level << ")" << std::endl;

  while(!done()) {
    Node assertion = get();
    Debug("uf") << "TheoryUFTim::check(): " << assertion << std::endl;

    switch(assertion.getKind()) {
    case EQUAL:
      d_assertions.push_back(assertion);
      d_pending.push_back(assertion);
      merge();
      break;
    case NOT:
      Assert(assertion[0].getKind() == EQUAL)
          << "predicates not supported in this UF implementation";
      d_disequality.push_back(assertion[0]);
      break;
    case APPLY_UF:
      Unhandled() << "predicates not supported in this UF implementation";
    default: Unhandled() << assertion.getKind();
    }

    Debug("uf") << "TheoryUFTim::check(): done = " << (done() ? "true" : "false") << std::endl;
  }

  //Make sure all outstanding merges are completed.
  if(d_currentPendingIdx < d_pending.size()) {
    merge();
  }

  if(standardEffortOrMore(level)) {
    for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
        diseqIter != d_disequality.end();
        ++diseqIter) {

      TNode left  = (*diseqIter)[0];
      TNode right = (*diseqIter)[1];
      if(sameCongruenceClass(left, right)) {
        Node remakeNeq = (*diseqIter).notNode();
        Node conflict = constructConflict(remakeNeq);
        d_out->conflict(conflict, false);
        return;
      }
    }
  }

  Debug("uf") << "uf: end check(" << level << ")" << std::endl;
}
