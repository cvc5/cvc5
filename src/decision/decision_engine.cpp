/*********************                                                        */
/*! \file decision_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

DecisionEngine::DecisionEngine(context::Context* sc, context::UserContext* uc)
    : d_enabledITEStrategies(),
      d_needIteSkolemMap(),
      d_relevancyStrategy(NULL),
      d_assertions(uc),
      d_cnfStream(NULL),
      d_satSolver(NULL),
      d_satContext(sc),
      d_userContext(uc),
      d_result(sc, SAT_VALUE_UNKNOWN),
      d_engineState(0)
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
    d_enabledITEStrategies.emplace_back(new decision::JustificationHeuristic(
        this, d_userContext, d_satContext));
    d_needIteSkolemMap.push_back(d_enabledITEStrategies.back().get());
  }
}

void DecisionEngine::shutdown()
{
  Trace("decision") << "Shutting down decision engine" << std::endl;

  Assert(d_engineState == 1);
  d_engineState = 2;

  d_enabledITEStrategies.clear();
  d_needIteSkolemMap.clear();
}

bool DecisionEngine::isRelevant(SatVariable var)
{
  Debug("decision") << "isRelevant(" << var <<")" << std::endl;
  if(d_relevancyStrategy != NULL) {
    //Assert(d_cnfStream->hasNode(var));
    return d_relevancyStrategy->isRelevant( d_cnfStream->getNode(SatLiteral(var)) );
  } else {
    return true;
  }
}

SatValue DecisionEngine::getPolarity(SatVariable var)
{
  Debug("decision") << "getPolarity(" << var <<")" << std::endl;
  if(d_relevancyStrategy != NULL) {
    Assert(isRelevant(var));
    return d_relevancyStrategy->getPolarity( d_cnfStream->getNode(SatLiteral(var)) );
  } else {
    return SAT_VALUE_UNKNOWN;
  }
}

void DecisionEngine::addAssertions(
    const preprocessing::AssertionPipeline& assertions)
{
  // new assertions, reset whatever result we knew
  d_result = SAT_VALUE_UNKNOWN;

  for (const Node& assertion : assertions)
  {
    d_assertions.push_back(assertion);
  }

  for(unsigned i = 0; i < d_needIteSkolemMap.size(); ++i)
  {
    d_needIteSkolemMap[i]->addAssertions(assertions);
  }
}

}/* CVC4 namespace */
