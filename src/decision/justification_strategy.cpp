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
                context::UserContext* u) : d_satContext(c), d_userContext(u), d_cnfStream(nullptr), d_satSolver(nullptr),
                d_assertions(u, c), d_skolemAssertions(c, c)
{
  
}

void JustificationStrategy::finishInit(prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs)
{
  d_satSolver = ss;
  d_cnfStream = cs;
}

prop::SatLiteral JustificationStrategy::getNext(bool& stopSearch)
{

}

bool JustificationStrategy::isDone()
{
  return false;
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


}/* CVC4 namespace */

