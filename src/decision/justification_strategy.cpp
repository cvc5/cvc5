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
      d_stackSizeValid(c, 0)
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
  // use main assertions, then skolem assertions
  if (setCurrentAssertion(d_assertions.getNextAssertion()))
  {
    return;
  }
  setCurrentAssertion(d_skolemAssertions.getNextAssertion());
}
bool JustificationStrategy::setCurrentAssertion(TNode c)
{
  if (c.isNull())
  {
    return false;
  }
  d_current = c;
  d_stackSizeValid = 0;
  return true;
}

JustifyInfo* JustificationStrategy::getOrAllocJustifyInfo(size_t i)
{
  // don't request stack beyond the bound
  Assert(i <= d_stack.size());
  if (i == d_stack.size())
  {
    d_stack.emplace_back(std::make_unique<JustifyInfo>(d_context));
  }
  return d_stack[i];
}

}  // namespace CVC4
