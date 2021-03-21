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

#define USING_OLD

namespace CVC4 {

DecisionEngine::DecisionEngine(context::Context* c,
                               context::UserContext* u,
                               ResourceManager* rm)
    : d_decEngineOld(new DecisionEngineOld(c, u)),
      d_jstrat(new JustificationStrategy(c, u)),
      d_resourceManager(rm)
{
}

void DecisionEngine::finishInit(prop::CDCLTSatSolverInterface* ss,
                                prop::CnfStream* cs)
{
#ifdef USING_OLD
  d_decEngineOld->setSatSolver(ss);
  d_decEngineOld->setCnfStream(cs);
  return;
#endif
  d_jstrat->finishInit(ss, cs);
}

prop::SatLiteral DecisionEngine::getNext(bool& stopSearch)
{
  d_resourceManager->spendResource(ResourceManager::Resource::DecisionStep);
#ifdef USING_OLD
  return d_decEngineOld->getNext(stopSearch);
#endif
  return d_jstrat->getNext(stopSearch);
}

bool DecisionEngine::isDone()
{
#ifdef USING_OLD
  return d_decEngineOld->isDone();
#endif
  return d_jstrat->isDone();
}

void DecisionEngine::addAssertion(TNode assertion)
{
#ifdef USING_OLD
  d_decEngineOld->addAssertion(assertion);
  return;
#endif
  d_jstrat->addAssertion(assertion);
}

void DecisionEngine::addSkolemDefinition(TNode lem, TNode skolem)
{
#ifdef USING_OLD
  d_decEngineOld->addSkolemDefinition(lem, skolem);
#endif
  // justification strategy does not use this
}

void DecisionEngine::notifyRelevantSkolemAssertion(TNode lem)
{
#ifdef USING_OLD
  return;
#endif
  // old implementation does not use this
  d_jstrat->notifyRelevantSkolemAssertion(lem);
}

}/* CVC4 namespace */
