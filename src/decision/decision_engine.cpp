/*********************                                                        */
/*! \file decision_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

using namespace std;

namespace CVC4 {

DecisionEngine::DecisionEngine(context::Context* sc,
                               context::UserContext* uc,
                               ResourceManager* rm)
    : d_cnfStream(nullptr),
      d_satSolver(nullptr),
      d_satContext(sc),
      d_userContext(uc),
      d_result(sc, SAT_VALUE_UNKNOWN),
      d_engineState(0),
      d_resourceManager(rm),
      d_enabledITEStrategy(nullptr)
{
  Trace("decision") << "Creating decision engine" << std::endl;
}

void DecisionEngine::init()
{
  Assert(d_engineState == 0);
  d_engineState = 1;

  Trace("decision-init") << "DecisionEngine::init()" << std::endl;
  Trace("decision-init") << " * options->decisionMode: "
                         << options::decisionMode() << std:: endl;
  Trace("decision-init") << " * options->decisionStopOnly: "
                         << options::decisionStopOnly() << std::endl;

  if (options::decisionMode() == options::DecisionMode::JUSTIFICATION)
  {
    d_enabledITEStrategy.reset(new decision::JustificationHeuristic(
        this, d_userContext, d_satContext));
  }
}

void DecisionEngine::shutdown()
{
  Trace("decision") << "Shutting down decision engine" << std::endl;

  Assert(d_engineState == 1);
  d_engineState = 2;
  d_enabledITEStrategy.reset(nullptr);
}

SatLiteral DecisionEngine::getNext(bool& stopSearch)
{
  d_resourceManager->spendResource(ResourceManager::Resource::DecisionStep);
  Assert(d_cnfStream != nullptr)
      << "Forgot to set cnfStream for decision engine?";
  Assert(d_satSolver != nullptr)
      << "Forgot to set satSolver for decision engine?";

  return d_enabledITEStrategy == nullptr
             ? undefSatLiteral
             : d_enabledITEStrategy->getNext(stopSearch);
}

void DecisionEngine::addAssertion(TNode assertion)
{
  // new assertions, reset whatever result we knew
  d_result = SAT_VALUE_UNKNOWN;
  if (d_enabledITEStrategy != nullptr)
  {
    d_enabledITEStrategy->addAssertion(assertion);
  }
}

void DecisionEngine::addSkolemDefinition(TNode lem, TNode skolem)
{
  // new assertions, reset whatever result we knew
  d_result = SAT_VALUE_UNKNOWN;
  if (d_enabledITEStrategy != nullptr)
  {
    d_enabledITEStrategy->addSkolemDefinition(lem, skolem);
  }
}

}/* CVC4 namespace */
