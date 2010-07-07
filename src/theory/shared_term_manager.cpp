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


SharedData* SharedTermManager::find(SharedData* pData) {
  SharedData* next = pData->getFind();
  if (next == pData) return pData;
  SharedData* nextNext = next->getFind();
  if (nextNext == next) return next;
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
  uint64_t newTags = parentTag | childTag;
  SharedData* pData;
  if(n.getAttribute(SharedAttr(), pData)) {
    // The attribute already exists, just update it if necessary
    uint64_t tags = pData->getTheories();
    newTags |= tags;
    if (tags == newTags) return;
    if (!(tags & parentTag)) {
      parent->addSharedTerm(n);
    }
    if (!(tags & childTag)) {
      child->addSharedTerm(n);
    }
    pData->setTheories(newTags);
  } else {
    // The attribute does not exist, so it is created and set
    pData = new (true) SharedData(d_context, n, newTags);
    n.setAttribute(SharedAttr(), pData);
    parent->addSharedTerm(n);
    child->addSharedTerm(n);
  }
}


void SharedTermManager::addEq(Theory* thReason, TNode eq) {
  Assert(eq.getKind() == kind::EQUAL &&
         eq[0].hasAttribute(SharedAttr()) && eq[1].hasAttribute(SharedAttr()),
         "SharedTermManager::addEq precondition violated");

  TNode x = eq[0];
  TNode y = eq[1];

  SharedData* pDataX = x.getAttribute(SharedAttr());
  SharedData* pDataY = y.getAttribute(SharedAttr());

  SharedData* pDataXX = find(pDataX);
  SharedData* pDataYY = find(pDataY);

  if(pDataXX == pDataYY) return;

  if(pDataXX->getSize() > pDataYY->getSize()) {
    SharedData* tmp = pDataXX;
    pDataXX = pDataYY;
    pDataYY = tmp;

    tmp = pDataX;
    pDataX = pDataY;
    pDataY = tmp;
  }

  pDataX->reverseEdges();
  pDataX->setEquality(eq);
  pDataX->setExplainingTheory(thReason);
  pDataX->setProofNext(pDataY);

  pDataXX->setFind(pDataYY);
  pDataYY->setSize(pDataYY->getSize() + pDataXX->getSize());
  uint64_t tags = pDataXX->getTheories();
  pDataYY->setTheories(pDataYY->getTheories() | tags);
  int id = 0;
  while (tags != 0) {
    if (tags & 1) {
      d_theories[id]->notifyEq(pDataXX->getRep(), pDataYY->getRep());
    }
    tags = tags >> 1;
    ++id;
  }
}


// Explain this equality
Node SharedTermManager::explain(TNode eq) {
  Assert(eq.getKind() == kind::EQUAL &&
         eq[0].hasAttribute(SharedAttr()) && eq[1].hasAttribute(SharedAttr()),
         "SharedTermManager::explain precondition violated");

  TNode x = eq[0];
  TNode y = eq[1];

  SharedData* pDataX = x.getAttribute(SharedAttr());
  SharedData* pDataY = y.getAttribute(SharedAttr());

  Assert(find(pDataX) == find(pDataY),
         "invalid equality input to SharedTermManager::explain");

  std::set<Node> s;
  Node n;
  SharedData* tmp = pDataX;

  // Check to see if Y is on path from X to root
  while (!tmp->isProofRoot() && tmp != pDataY) {
    tmp = tmp->getProofNext();
  }
  if (tmp == pDataY) {
    // Y is on path from X to root, just traverse that path
    while (pDataX != pDataY) {
      n = d_engine->getExplanation(pDataX->getEquality(),
                                   pDataX->getExplainingTheory());
      for (Node::iterator it = n.begin(), iend = n.end(); it != iend; ++it) {
        s.insert(*it);
      }
      pDataX = pDataX->getProofNext();
    }
  }
  else {
    // Y is not on path from X to root, so traverse from Y to root instead
    while (!pDataY->isProofRoot() && pDataX != pDataY) {
      n = d_engine->getExplanation(pDataY->getEquality(),
                                   pDataY->getExplainingTheory());
      for (Node::iterator it = n.begin(), iend = n.end(); it != iend; ++it) {
        s.insert(*it);
      }
      pDataY = pDataY->getProofNext();
    }
  }
  if (pDataX != pDataY) {
    // X and Y are on different branches - have to traverse both
    while (!pDataX->isProofRoot()) {
      n = d_engine->getExplanation(pDataX->getEquality(),
                                   pDataX->getExplainingTheory());
      for (Node::iterator it = n.begin(), iend = n.end(); it != iend; ++it) {
        s.insert(*it);
      }
      pDataX = pDataX->getProofNext();
    }
  }

  // Build explanation from s
  NodeBuilder<kind::AND> nb;
  set<Node>::iterator it = s.begin(), iend = s.end();
  for (; it != iend; ++it) {
    nb << *it;
  }
  return nb.constructNode();
}


}/* CVC4 namespace */
