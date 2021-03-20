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

#include "decision/decision_attributes.h"
#include "decision/justification_heuristic.h"
#include "expr/node.h"
#include "options/decision_options.h"
#include "options/smt_options.h"
#include "util/resource_manager.h"

using namespace std;

namespace CVC4 {

DecisionEngine::DecisionEngine(context::Context* sc,
                               context::UserContext* uc,
                               ResourceManager* rm)
    : d_usingOld(true),
      d_decEngineOld(new DecisionEngineOld(sc, uc, rm)),
      d_cnfStream(nullptr),
      d_satSolver(nullptr),
      d_satContext(sc),
      d_userContext(uc),
      d_resourceManager(rm)
{
}

void DecisionEngine::finishInit(CDCLTSatSolverInterface* ss, CnfStream* cs)
{
  d_satSolver = ss;
  d_cnfStream = cs;
  if (d_usingOld)
  {
    d_decEngineOld->setSatSolver(ss);
    d_decEngineOld->setCnfStream(cs);
  }
}

void DecisionEngine::shutdown()
{
  if (d_usingOld)
  {
    d_decEngineOld->shutdown();
  }
}

SatLiteral DecisionEngine::getNext(bool& stopSearch)
{
  d_resourceManager->spendResource(ResourceManager::Resource::DecisionStep);
  if (d_usingOld)
  {
    return d_decEngineOld->getNext(stopSearch);
  }
  // FIXME
  return d_decEngineOld->getNext(stopSearch);
}

bool DecisionEngine::isDone() {
  if (d_usingOld)
  {
    return d_decEngineOld->isDone();
  }
  // FIXME
  return false;
}

/*
void DecisionEngine::setResult(SatValue val) {
  d_result = val;
}
*/

void DecisionEngine::addAssertion(TNode assertion)
{
  if (d_usingOld)
  {
    d_decEngineOld->addAssertion(assertion);
  }
}

void DecisionEngine::addSkolemDefinition(TNode lem, TNode skolem)
{
  if (d_usingOld)
  {
    d_decEngineOld->addSkolemDefinition(lem, skolem);
  }
}

bool DecisionEngine::hasSatLiteral(TNode n) {
  return d_cnfStream->hasLiteral(n);
}
SatLiteral DecisionEngine::getSatLiteral(TNode n) {
  return d_cnfStream->getLiteral(n);
}
SatValue DecisionEngine::getSatValue(SatLiteral l) {
  return d_satSolver->value(l);
}
SatValue DecisionEngine::getSatValue(TNode n) {
  return getSatValue(getSatLiteral(n));
}
Node DecisionEngine::getNode(SatLiteral l) {
  return d_cnfStream->getNode(l);
}

}/* CVC4 namespace */
