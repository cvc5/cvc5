/*********************                                                        */
/*! \file decision_engine.cpp
 ** \verbatim
 ** Original author: kshitij
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Decision engine
 **
 ** Decision engine
 **/

#include "decision/decision_engine.h"
#include "decision/justification_heuristic.h"

#include "expr/node.h"
#include "util/options.h"

using namespace std;

namespace CVC4 {

DecisionEngine::DecisionEngine(context::Context *c) :
  d_enabledStrategies(),
  d_needSimplifiedPreITEAssertions(),
  d_assertions(),
  d_cnfStream(NULL),
  d_satSolver(NULL),
  d_satContext(c),
  d_result(SAT_VALUE_UNKNOWN)
{
  const Options* options = Options::current();
  Trace("decision") << "Creating decision engine" << std::endl;

  if(options->incrementalSolving) return;

  if(options->decisionMode == Options::DECISION_STRATEGY_INTERNAL) { }
  if(options->decisionMode == Options::DECISION_STRATEGY_JUSTIFICATION) {
    DecisionStrategy* ds = new decision::JustificationHeuristic(this, d_satContext);
    enableStrategy(ds);
  }
}

void DecisionEngine::enableStrategy(DecisionStrategy* ds)
{
  d_enabledStrategies.push_back(ds);
  if( ds->needSimplifiedPreITEAssertions() )
    d_needSimplifiedPreITEAssertions.push_back(ds);
}

void DecisionEngine::informSimplifiedPreITEAssertions(const vector<Node> &assertions)
{
  d_result = SAT_VALUE_UNKNOWN;
  d_assertions.reserve(assertions.size());
  for(unsigned i = 0; i < assertions.size(); ++i)
    d_assertions.push_back(assertions[i]);
  for(unsigned i = 0; i < d_needSimplifiedPreITEAssertions.size(); ++i)
    d_needSimplifiedPreITEAssertions[i]->notifyAssertionsAvailable();
}

void DecisionEngine::addAssertion(Node n)
{
  d_result = SAT_VALUE_UNKNOWN;
  if(needSimplifiedPreITEAssertions()) {
    d_assertions.push_back(n);
  }
  for(unsigned i = 0; i < d_needSimplifiedPreITEAssertions.size(); ++i)
    d_needSimplifiedPreITEAssertions[i]->notifyAssertionsAvailable();
}
  

}/* CVC4 namespace */
