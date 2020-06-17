/*********************                                                        */
/*! \file theory_sets.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory.
 **
 ** Sets theory.
 **/

#include "theory/sets/theory_sets.h"

#include "options/sets_options.h"
#include "theory/sets/theory_sets_private.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

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

TheoryRewriter* TheorySets::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

void TheorySets::finishInit()
{
  TheoryModel* tm = d_valuation.getModel();
  Assert(tm != nullptr);
  tm->setUnevaluatedKind(COMPREHENSION);
  // choice is used to eliminate witness
  tm->setUnevaluatedKind(WITNESS);
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

Node TheorySets::expandDefinition(Node n)
{
  Kind nk = n.getKind();
  if (nk == UNIVERSE_SET || nk == COMPLEMENT || nk == JOIN_IMAGE
      || nk == COMPREHENSION)
  {
    if (!options::setsExt())
    {
      std::stringstream ss;
      ss << "Extended set operators are not supported in default mode, try "
            "--sets-ext.";
      throw LogicException(ss.str());
    }
  }
  if (nk == COMPREHENSION)
  {
    // set comprehension is an implicit quantifier, require it in the logic
    if (!getLogicInfo().isQuantified())
    {
      std::stringstream ss;
      ss << "Set comprehensions require quantifiers in the background logic.";
      throw LogicException(ss.str());
    }
  }
  return d_internal->expandDefinition(n);
}

Theory::PPAssertStatus TheorySets::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  Debug("sets-proc") << "ppAssert : " << in << std::endl;
  Theory::PPAssertStatus status = Theory::PP_ASSERT_STATUS_UNSOLVED;

  // this is based off of Theory::ppAssert
  if (in.getKind() == kind::EQUAL)
  {
    if (in[0].isVar() && isLegalElimination(in[0], in[1]))
    {
      // We cannot solve for sets if setsExt is enabled, since universe set
      // may appear when this option is enabled, and solving for such a set
      // impacts the semantics of universe set, see
      // regress0/sets/pre-proc-univ.smt2
      if (!in[0].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitution(in[0], in[1]);
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[1].isVar() && isLegalElimination(in[1], in[0]))
    {
      if (!in[0].getType().isSet() || !options::setsExt())
      {
        outSubstitutions.addSubstitution(in[1], in[0]);
        status = Theory::PP_ASSERT_STATUS_SOLVED;
      }
    }
    else if (in[0].isConst() && in[1].isConst())
    {
      if (in[0] != in[1])
      {
        status = Theory::PP_ASSERT_STATUS_CONFLICT;
      }
    }
  }
  return status;
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
