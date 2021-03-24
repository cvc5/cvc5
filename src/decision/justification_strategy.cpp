/*********************                                                        */
/*! \file justification_strategy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification strategy
 **/

#include "decision/justification_strategy.h"

using namespace CVC4::kind;

namespace CVC4 {

JustificationStrategy::JustificationStrategy(context::Context* c,
                                             context::UserContext* u)
    : d_context(c),
      d_cnfStream(nullptr),
      d_satSolver(nullptr),
      d_assertions(u, c),        // assertions are user-context dependent
      d_skolemAssertions(c, c),  // skolem assertions are SAT-context dependent
      d_current(c),
      d_justified(c),
      d_stack(c),
      d_stackIndex(c, 0)
{
}

void JustificationStrategy::finishInit(prop::CDCLTSatSolverInterface* ss,
                                       prop::CnfStream* cs)
{
  d_satSolver = ss;
  d_cnfStream = cs;
}

prop::SatLiteral JustificationStrategy::getNext(bool& stopSearch)
{
  // ensure we have an assertion
  refreshCurrentAssertion();
  // get the current justify info
  Assert (d_stack.size()>d_stackIndex.get());
  JustifyInfo * ji = d_stack[d_stackIndex.get()].get();
  
  // TODO
}

bool JustificationStrategy::isDone()
{
  refreshCurrentAssertion();
  return d_current.get().isNull();
}

void JustificationStrategy::addAssertion(TNode assertion)
{
  d_assertions.addAssertion(assertion);
}

void JustificationStrategy::notifyRelevantSkolemAssertion(TNode lem)
{
  d_skolemAssertions.addAssertion(lem);
}

bool JustificationStrategy::hasSatLiteral(TNode n)
{
  return d_cnfStream->hasLiteral(n);
}

prop::SatLiteral JustificationStrategy::getSatLiteral(TNode n)
{
  return d_cnfStream->getLiteral(n);
}

prop::SatValue JustificationStrategy::getSatValue(prop::SatLiteral l)
{
  return d_satSolver->value(l);
}

prop::SatValue JustificationStrategy::getSatValue(TNode n)
{
  return getSatValue(getSatLiteral(n));
}

Node JustificationStrategy::getNode(prop::SatLiteral l)
{
  return d_cnfStream->getNode(l);
}

void JustificationStrategy::refreshCurrentAssertion()
{
  // if we already have a current assertion, nothing to be done
  if (!d_current.get().isNull())
  {
    return;
  }
  // use main assertions first
  if (setCurrentAssertion(d_assertions.getNextAssertion()))
  {
    return;
  }
  // if satisfied all main assertions, use the skolem assertions
  setCurrentAssertion(d_skolemAssertions.getNextAssertion());
}

bool JustificationStrategy::setCurrentAssertion(TNode c)
{
  if (c.isNull())
  {
    return false;
  }
  d_current = c;
  // set up the initial info: we want to set the atom of c to its polarity
  bool pol = c.getKind()!=NOT;
  TNode atom = pol ? c : c[0];
  Assert (catom.getKind()!=NOT);
  JustifyInfo* ji = getOrAllocJustifyInfo(0);
  ji->set(atom, pol ? prop::SAT_VALUE_TRUE : prop::SAT_VALUE_FALSE);
  d_stackIndex = 0;
  return true;
}

JustifyInfo* JustificationStrategy::getOrAllocJustifyInfo(size_t i)
{
  // don't request stack beyond the bound
  Assert(i <= d_stack.size());
  if (i == d_stack.size())
  {
    d_stack.push_back(std::make_shared<JustifyInfo>(d_context));
  }
  return d_stack[i].get();
}

}  // namespace CVC4
