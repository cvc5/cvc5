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
 * Old implementation of the decision engine
 */
#include "decision/decision_engine_old.h"

#include "decision/decision_attributes.h"
#include "decision/justification_heuristic.h"
#include "expr/node.h"
#include "options/decision_options.h"
#include "options/smt_options.h"
#include "util/resource_manager.h"

using namespace std;

namespace cvc5 {

DecisionEngineOld::DecisionEngineOld(context::Context* sc,
                                     context::UserContext* uc,
                                     ResourceManager* rm)
    : DecisionEngine(sc, rm),
      d_result(sc, SAT_VALUE_UNKNOWN),
      d_engineState(0),
      d_enabledITEStrategy(nullptr),
      d_decisionStopOnly(options::decisionMode()
                         == options::DecisionMode::STOPONLY_OLD)
{
  Trace("decision") << "Creating decision engine" << std::endl;
  Assert(d_engineState == 0);
  d_engineState = 1;

  Trace("decision-init") << "DecisionEngineOld::init()" << std::endl;
  Trace("decision-init") << " * options->decisionMode: "
                         << options::decisionMode() << std::endl;
  Trace("decision-init") << " * decisionStopOnly: " << d_decisionStopOnly
                         << std::endl;

  if (options::decisionMode() == options::DecisionMode::JUSTIFICATION)
  {
    d_enabledITEStrategy.reset(
        new decision::JustificationHeuristic(this, uc, sc));
  }
}

void DecisionEngineOld::shutdown()
{
  Trace("decision") << "Shutting down decision engine" << std::endl;

  Assert(d_engineState == 1);
  d_engineState = 2;
  d_enabledITEStrategy.reset(nullptr);
}

SatLiteral DecisionEngineOld::getNextInternal(bool& stopSearch)
{
  Assert(d_cnfStream != nullptr)
      << "Forgot to set cnfStream for decision engine?";
  Assert(d_satSolver != nullptr)
      << "Forgot to set satSolver for decision engine?";

  SatLiteral ret = d_enabledITEStrategy == nullptr
                       ? undefSatLiteral
                       : d_enabledITEStrategy->getNext(stopSearch);
  // if we are doing stop only, we don't return the literal
  return d_decisionStopOnly ? undefSatLiteral : ret;
}

void DecisionEngineOld::addAssertion(TNode assertion)
{
  // new assertions, reset whatever result we knew
  d_result = SAT_VALUE_UNKNOWN;
  if (d_enabledITEStrategy != nullptr)
  {
    d_enabledITEStrategy->addAssertion(assertion);
  }
}

void DecisionEngineOld::addSkolemDefinition(TNode lem, TNode skolem)
{
  // new assertions, reset whatever result we knew
  d_result = SAT_VALUE_UNKNOWN;
  if (d_enabledITEStrategy != nullptr)
  {
    d_enabledITEStrategy->addSkolemDefinition(lem, skolem);
  }
}

}  // namespace cvc5
