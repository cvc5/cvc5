/*********************                                                        */
/*! \file justification_strategy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Morgan Deters
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
                context::UserContext* u) : d_satContext(c), d_userContext(u), d_cnfStream(nullptr), d_satSolver(nullptr)
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

void addAssertion(TNode assertion)
{
  
}

void notifyRelevantAssertion(TNode lem)
{
  
}

bool DecisionEngine::hasSatLiteral(TNode n)
{
  return d_cnfStream->hasLiteral(n);
}

prop::SatLiteral DecisionEngine::getSatLiteral(TNode n)
{
  return d_cnfStream->getLiteral(n);
}

prop::SatValue DecisionEngine::getSatValue(prop::SatLiteral l)
{
  return d_satSolver->value(l);
}

prop::SatValue DecisionEngine::getSatValue(TNode n)
{
  return getSatValue(getSatLiteral(n));
}

Node DecisionEngine::getNode(prop::SatLiteral l)
{
  return d_cnfStream->getNode(l);
}


}/* CVC4 namespace */

