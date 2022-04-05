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

#include "util/resource_manager.h"

namespace cvc5::internal {
namespace decision {

DecisionEngine::DecisionEngine(Env& env)
    : EnvObj(env), d_cnfStream(nullptr), d_satSolver(nullptr)
{
}

void DecisionEngine::finishInit(prop::CDCLTSatSolverInterface* ss,
                                prop::CnfStream* cs)
{
  d_satSolver = ss;
  d_cnfStream = cs;
}

prop::SatLiteral DecisionEngine::getNext(bool& stopSearch)
{
  resourceManager()->spendResource(Resource::DecisionStep);
  return getNextInternal(stopSearch);
}

DecisionEngineEmpty::DecisionEngineEmpty(Env& env) : DecisionEngine(env) {}
bool DecisionEngineEmpty::isDone() { return false; }
void DecisionEngineEmpty::addAssertion(TNode assertion, bool isLemma) {}
void DecisionEngineEmpty::addSkolemDefinition(TNode lem,
                                              TNode skolem,
                                              bool isLemma)
{
}
prop::SatLiteral DecisionEngineEmpty::getNextInternal(bool& stopSearch)
{
  return prop::undefSatLiteral;
}

}  // namespace decision
}  // namespace cvc5::internal
