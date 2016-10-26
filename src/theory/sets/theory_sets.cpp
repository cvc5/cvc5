/*********************                                                        */
/*! \file theory_sets.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory.
 **
 ** Sets theory.
 **/

#include "theory/sets/theory_sets.h"
#include "theory/sets/theory_sets_private.h"

namespace CVC4 {
namespace theory {
namespace sets {

TheorySets::TheorySets(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo)
    : Theory(THEORY_SETS, c, u, out, valuation, logicInfo),
      d_internal(new TheorySetsPrivate(*this, c, u))
{}

TheorySets::~TheorySets() {
  delete d_internal;
}

void TheorySets::addSharedTerm(TNode n) {
  d_internal->addSharedTerm(n);
}

void TheorySets::check(Effort e) {
  if (done() && !fullEffort(e)) {
    return;
  }
  TimerStat::CodeTimer checkTimer(d_checkTime);
  d_internal->check(e);
}

void TheorySets::collectModelInfo(TheoryModel* m, bool fullModel) {
  d_internal->collectModelInfo(m, fullModel);
}

void TheorySets::computeCareGraph() {
  d_internal->computeCareGraph();
}

Node TheorySets::explain(TNode node) {
  return d_internal->explain(node);
}

EqualityStatus TheorySets::getEqualityStatus(TNode a, TNode b) {
  return d_internal->getEqualityStatus(a, b);
}

Node TheorySets::getModelValue(TNode node) {
  return Node::null();
}

void TheorySets::preRegisterTerm(TNode node) {
  d_internal->preRegisterTerm(node);
}

void TheorySets::presolve() {
  d_internal->presolve();
}

void TheorySets::propagate(Effort e) {
  d_internal->propagate(e);
}

void TheorySets::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_internal->setMasterEqualityEngine(eq);
}

bool TheorySets::isEntailed( Node n, bool pol ) {
  return d_internal->isEntailed( n, pol );
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
