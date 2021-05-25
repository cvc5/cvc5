/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Decision engine.
 */
#include "decision/decision_engine.h"

#include "decision/decision_engine_old.h"
#include "options/decision_options.h"
#include "prop/sat_solver.h"
#include "util/resource_manager.h"

namespace cvc5 {
namespace decision {

DecisionEngine::DecisionEngine(context::Context* c,
                               context::UserContext* u,
                               prop::SkolemDefManager* skdm,
                               ResourceManager* rm)
    : d_decEngineOld(new DecisionEngineOld(c, u)),
      d_resourceManager(rm),
      d_useOld(true)
{
}

void DecisionEngine::finishInit(prop::CDCLTSatSolverInterface* ss,
                                prop::CnfStream* cs)
{
  if (d_useOld)
  {
    d_decEngineOld->setSatSolver(ss);
    d_decEngineOld->setCnfStream(cs);
    return;
  }
}

void DecisionEngine::presolve() {}

prop::SatLiteral DecisionEngine::getNext(bool& stopSearch)
{
  d_resourceManager->spendResource(Resource::DecisionStep);
  if (d_useOld)
  {
    return d_decEngineOld->getNext(stopSearch);
  }
  return undefSatLiteral;
}

bool DecisionEngine::isDone()
{
  if (d_useOld)
  {
    return d_decEngineOld->isDone();
  }
  return false;
}

void DecisionEngine::addAssertion(TNode assertion)
{
  if (d_useOld)
  {
    d_decEngineOld->addAssertion(assertion);
    return;
  }
}

void DecisionEngine::addSkolemDefinition(TNode lem, TNode skolem)
{
  if (d_useOld)
  {
    d_decEngineOld->addSkolemDefinition(lem, skolem);
  }
}

void DecisionEngine::notifyAsserted(TNode n)
{
  if (d_useOld)
  {
    return;
  }
}

}  // namespace decision
}  // namespace cvc5
