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

DecisionEngine::DecisionEngine(context::Context* c, ResourceManager* rm)
    : d_context(c),
      d_resourceManager(rm),
      d_cnfStream(nullptr),
      d_satSolver(nullptr)
{
}

void DecisionEngine::finishInit(CDCLTSatSolverInterface* ss, CnfStream* cs)
{
  d_satSolver = ss;
  d_cnfStream = cs;
}

prop::SatLiteral DecisionEngine::getNext(bool& stopSearch)
{
  d_resourceManager->spendResource(Resource::DecisionStep);
  return getNextInternal(stopSearch);
}

DecisionEngineEmpty::DecisionEngineEmpty(context::Context* sc,
                                         ResourceManager* rm)
    : DecisionEngine(sc, rm)
{
}
bool DecisionEngineEmpty::isDone() { return false; }
void DecisionEngineEmpty::addAssertion(TNode assertion) {}
void DecisionEngineEmpty::addSkolemDefinition(TNode lem, TNode skolem) {}
prop::SatLiteral DecisionEngineEmpty::getNextInternal(bool& stopSearch)
{
  return undefSatLiteral;
}

}  // namespace decision
}  // namespace cvc5
