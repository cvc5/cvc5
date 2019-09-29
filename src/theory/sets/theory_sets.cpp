/*********************                                                        */
/*! \file theory_sets.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
{
  // Do not move me to the header.
  // The constructor + destructor are not in the header as d_internal is a
  // unique_ptr<TheorySetsPrivate> and TheorySetsPrivate is an opaque type in
  // the header (Pimpl). See https://herbsutter.com/gotw/_100/ .
}

TheorySets::~TheorySets()
{
  // Do not move me to the header. See explanation in the constructor.
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

bool TheorySets::collectModelInfo(TheoryModel* m)
{
  return d_internal->collectModelInfo(m);
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
