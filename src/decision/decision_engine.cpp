/*********************                                                        */
/*! \file decision_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Aina Niemetz, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Decision engine
 **
 ** Decision engine
 **/
#include "decision/decision_engine.h"

#include "decision/decision_engine_old.h"
#include "prop/sat_solver.h"
#include "util/resource_manager.h"

using namespace std;

namespace CVC4 {

DecisionEngine::DecisionEngine(context::Context* c,
                               context::UserContext* u,
                               ResourceManager* rm)
    : d_usingOld(true),
      d_decEngineOld(new DecisionEngineOld(c, u)),
      d_jstrat(new JustificationStrategy(c, u)),
      d_resourceManager(rm)
{
}

void DecisionEngine::finishInit(prop::CDCLTSatSolverInterface* ss,
                                prop::CnfStream* cs)
{
  if (d_usingOld)
  {
    d_decEngineOld->setSatSolver(ss);
    d_decEngineOld->setCnfStream(cs);
  }
  else
  {
    d_jstrat->finishInit(ss, cs);
  }
}

prop::SatLiteral DecisionEngine::getNext(bool& stopSearch)
{
  d_resourceManager->spendResource(ResourceManager::Resource::DecisionStep);
  if (d_usingOld)
  {
    return d_decEngineOld->getNext(stopSearch);
  }
  return d_jstrat->getNext(stopSearch);
}

bool DecisionEngine::isDone()
{
  if (d_usingOld)
  {
    return d_decEngineOld->isDone();
  }
  return d_jstrat->isDone();
}

void DecisionEngine::addAssertion(TNode assertion)
{
  if (d_usingOld)
  {
    d_decEngineOld->addAssertion(assertion);
  }
  else
  {
    d_jstrat->addAssertion(assertion);
  }
}

void DecisionEngine::addSkolemDefinition(TNode lem, TNode skolem)
{
  if (d_usingOld)
  {
    d_decEngineOld->addSkolemDefinition(lem, skolem);
  }
  // justification strategy does not use this
}

void DecisionEngine::notifyRelevantAssertion(TNode lem)
{
  // old implementation does not use this
  if (!d_usingOld)
  {
    d_jstrat->addSkolemDefinition(lem, skolem);
  }
}


}/* CVC4 namespace */
