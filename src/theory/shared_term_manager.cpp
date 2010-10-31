/*********************                                                        */
/*! \file shared_term_manager.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The shared term manager
 **
 ** The shared term manager
 **/

#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {


SharedTermManager::SharedTermManager(TheoryEngine* engine,
                                     context::Context* context)
  : d_engine(engine), d_context(context), d_theories(64) {
}


SharedData* SharedTermManager::find(SharedData* pData) const {
  // Check if pData is the representative
  SharedData* next = pData->getFind();
  if (next == pData) return pData;

  // Check if its successor is the representative
  SharedData* nextNext = next->getFind();
  if (nextNext == next) return next;

  // Otherwise, recurse and do find path-compression
  next = find(nextNext);
  pData->setFind(next);
  return next;
}


void SharedTermManager::registerTheory(Theory* th) {
  Assert(th->getId() < 64, "Theory ID out of bounds");
  d_theories[th->getId()] = th;
}


void SharedTermManager::addTerm(TNode n, Theory* parent, Theory* child) {
  Assert(parent->getId() < 64 && child->getId() < 64,
         "Theory ID out of bounds");
  Assert(d_theories[parent->getId()] == parent &&
         d_theories[child->getId()] == child,
         "Theory not registered");

  // A theory tag is represented by a 1 in the i^th bit where i is the
  // theory id
  uint64_t parentTag = (1 << parent->getId());
  uint64_t childTag = (1 << child->getId());
  uint64_t bothTags = parentTag | childTag;

  // Create or update the SharedData for n
  SharedData* pData;
  if(n.getAttribute(SharedAttr(), pData)) {
    // The attribute already exists, just update it if necessary
    uint64_t tags = pData->getTheories();
    uint64_t newTags = tags | bothTags;
    if (tags == newTags) return;

    // Get the equivalence class representative -- if this is different from
    // the current node, then we will need to notify the theories of that and
    // update the theory tags on the representative node
    SharedData* pDataFind = find(pData);

    // Notify parent theory if necessary
    if (!(tags & parentTag)) {
      parent->addSharedTerm(n);
      if (pData != pDataFind) {
        parent->notifyEq(n, pDataFind->getRep());
      }
    }

    // Notify child theory if necessary
    if (!(tags & childTag)) {
      child->addSharedTerm(n);
      if (pData != pDataFind) {
        child->notifyEq(n, pDataFind->getRep());
      }
    }

    // Update theory tags
    pData->setTheories(newTags);
    if (pData != pDataFind) {
      tags = pDataFind->getTheories();
      newTags = tags | bothTags;
      if (tags != newTags) {
        pDataFind->setTheories(newTags);
      }
    }
  } else {
    // The attribute does not exist, so it is created and set
    pData = new (true) SharedData(d_context, n, bothTags);
    n.setAttribute(SharedAttr(), pData);
    parent->addSharedTerm(n);
    child->addSharedTerm(n);
  }
}


void SharedTermManager::addEq(TNode eq, Theory* thReason) {
  Assert(eq.getKind() == kind::EQUAL,
         "SharedTermManager::addEq precondition violated");

  TNode x = eq[0];
  TNode y = eq[1];

  SharedData* pDataX;
  SharedData* pDataY;

  // Grab the SharedData for each side of the equality, create if necessary
  if(!x.getAttribute(SharedAttr(), pDataX)) {
    pDataX = new (true) SharedData(d_context, x, 0);
    x.setAttribute(SharedAttr(), pDataX);
  }
  if(!y.getAttribute(SharedAttr(), pDataY)) {
    pDataY = new (true) SharedData(d_context, y, 0);
    y.setAttribute(SharedAttr(), pDataY);
  }

  // Get the representatives
  SharedData* pDataXX = find(pDataX);
  SharedData* pDataYY = find(pDataY);

  // If already in the same equivalence class, nothing to do
  if(pDataXX == pDataYY) return;

  // Make sure we reverse the edges in the smaller tree
  bool switched = false;
  if(pDataXX->getSize() > pDataYY->getSize()) {
    SharedData* tmp = pDataXX;
    pDataXX = pDataYY;
    pDataYY = tmp;

    tmp = pDataX;
    pDataX = pDataY;
    pDataY = tmp;

    switched = true;
  }

  // Reverse the edges in the left proof tree and link the two trees
  if(!pDataX->isProofRoot()) {
    pDataX->reverseEdges();
  }
  pDataX->setEdgeReversed(switched);
  pDataX->setExplainingTheory(thReason);
  pDataX->setProofNext(pDataY);

  // Set the equivalence class representative for the left node to be the right node
  pDataXX->setFind(pDataYY);
  pDataYY->setSize(pDataYY->getSize() + pDataXX->getSize());

  // Update the theory tags for the new representative
  uint64_t tags = pDataXX->getTheories();
  pDataYY->setTheories(pDataYY->getTheories() | tags);

  // Notify the theories that care about the left node
  int id = 0;
  while (tags != 0) {
    if (tags & 1) {
      d_theories[id]->notifyEq(pDataXX->getRep(), pDataYY->getRep());
    }
    tags = tags >> 1;
    ++id;
  }
}


void SharedTermManager::collectExplanations(SharedData* pData, std::set<Node>& s) const {
  Theory* expTh = pData->getExplainingTheory();
  if(expTh == NULL) {
    // This equality is directly from SAT, no need to ask a theory for an explanation
    s.insert(pData->getEquality());
  }
  else {
    // This equality was sent by a theory - ask the theory for the explanation
    Node n = d_engine->getExplanation(pData->getEquality(), expTh);
    if(n.getKind() == kind::AND) {
      for (Node::iterator it = n.begin(), iend = n.end(); it != iend; ++it) {
        s.insert(*it);
      }
    }
    else {
      s.insert(n);
    }
  }
}


// Explain this equality
Node SharedTermManager::explain(TNode eq) const {
  Assert(eq.getKind() == kind::EQUAL &&
         eq[0].hasAttribute(SharedAttr()) && eq[1].hasAttribute(SharedAttr()),
         "SharedTermManager::explain precondition violated");

  TNode x = eq[0];
  TNode y = eq[1];

  // Get the SharedData for both sides of the equality
  SharedData* pDataX = x.getAttribute(SharedAttr());
  SharedData* pDataY = y.getAttribute(SharedAttr());

  Assert(find(pDataX) == find(pDataY),
         "invalid equality input to SharedTermManager::explain");

  // Find the path between the two nodes and build up the explanation
  std::set<Node> s;
  SharedData* tmp = pDataX;

  // Check to see if Y is on path from X to root
  while (!tmp->isProofRoot() && tmp != pDataY) {
    tmp = tmp->getProofNext();
  }
  if (tmp == pDataY) {
    // Y is on path from X to root, just traverse that path
    while (pDataX != pDataY) {
      collectExplanations(pDataX, s);
      pDataX = pDataX->getProofNext();
    }
  }
  else {
    // Y is not on path from X to root, so traverse from Y to root instead
    while (!pDataY->isProofRoot() && pDataX != pDataY) {
      collectExplanations(pDataY, s);
      pDataY = pDataY->getProofNext();
    }
  }
  if (pDataX != pDataY) {
    // X and Y are on different branches - have to traverse both
    while (!pDataX->isProofRoot()) {
      collectExplanations(pDataX, s);
      pDataX = pDataX->getProofNext();
    }
  }

  // Build explanation from s
  NodeBuilder<> nb(kind::AND);
  set<Node>::iterator it = s.begin(), iend = s.end();
  for (; it != iend; ++it) {
    nb << *it;
  }
  return nb.constructNode();
}


Node SharedTermManager::getRep(TNode n) const {
  Assert(n.hasAttribute(SharedAttr()),
         "SharedTermManager::getRep precondition violated");

  SharedData* pData = n.getAttribute(SharedAttr());
  return find(pData)->getRep();
}


}/* CVC4 namespace */
