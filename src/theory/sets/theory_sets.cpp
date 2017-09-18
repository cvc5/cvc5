/*********************                                                        */
/*! \file theory_sets.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
  if (done() && e < Theory::EFFORT_FULL) {
    return;
  }
  TimerStat::CodeTimer checkTimer(d_checkTime);
  d_internal->check(e);
}

bool TheorySets::needsCheckLastEffort() {
  return d_internal->needsCheckLastEffort();
}

void TheorySets::collectModelInfo(TheoryModel* m) {
  d_internal->collectModelInfo(m);
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

Node TheorySets::expandDefinition(LogicRequest &logicRequest, Node n) {
  return d_internal->expandDefinition(logicRequest, n);
}

Theory::PPAssertStatus TheorySets::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  return d_internal->ppAssert( in, outSubstitutions );
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
