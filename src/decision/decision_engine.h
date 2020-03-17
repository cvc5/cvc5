/*********************                                                        */
/*! \file decision_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Morgan Deters, Tim King
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

#include "cvc4_private.h"

#ifndef CVC4__DECISION__DECISION_ENGINE_H
#define CVC4__DECISION__DECISION_ENGINE_H

#include <vector>

#include "base/output.h"
#include "decision/decision_strategy.h"
#include "expr/node.h"
#include "preprocessing/assertion_pipeline.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat_solver_types.h"
#include "smt/smt_engine_scope.h"
#include "smt/term_formula_removal.h"

using namespace std;
using namespace CVC4::prop;
using namespace CVC4::decision;

namespace CVC4 {

class DecisionEngine {
  std::unique_ptr<ITEDecisionStrategy> d_enabledITEStrategy;
  vector <ITEDecisionStrategy* > d_needIteSkolemMap;
  RelevancyStrategy* d_relevancyStrategy;

  typedef context::CDList<Node> AssertionsList;
  AssertionsList d_assertions;

  // PropEngine* d_propEngine;
  CnfStream* d_cnfStream;
  DPLLSatSolverInterface* d_satSolver;

  context::Context* d_satContext;
  context::UserContext* d_userContext;

  // Does decision engine know the answer?
  context::CDO<SatValue> d_result;

  // Disable creating decision engine without required parameters
  DecisionEngine();

  // init/shutdown state
  unsigned d_engineState;    // 0=pre-init; 1=init,pre-shutdown; 2=shutdown
public:
  // Necessary functions

  /** Constructor */
  DecisionEngine(context::Context *sc, context::UserContext *uc);

  /** Destructor, currently does nothing */
  ~DecisionEngine() {
    Trace("decision") << "Destroying decision engine" << std::endl;
  }

  void setSatSolver(DPLLSatSolverInterface* ss) {
    // setPropEngine should not be called more than once
    Assert(d_satSolver == NULL);
    Assert(ss != NULL);
    d_satSolver = ss;
  }

  void setCnfStream(CnfStream* cs) {
    // setPropEngine should not be called more than once
    Assert(d_cnfStream == NULL);
    Assert(cs != NULL);
    d_cnfStream = cs;
  }

  /* Enables decision strategy based on options. */
  void init();

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system.
   */
  void shutdown();

  // Interface for External World to use our services

  /** Gets the next decision based on strategies that are enabled */
  SatLiteral getNext(bool& stopSearch);

  /** Is a sat variable relevant */
  bool isRelevant(SatVariable var);

  /**
   * Try to get tell SAT solver what polarity to try for a
   * decision. Return SAT_VALUE_UNKNOWN if it can't help
   */
  SatValue getPolarity(SatVariable var);

  /** Is the DecisionEngine in a state where it has solved everything? */
  bool isDone() {
    Trace("decision") << "DecisionEngine::isDone() returning "
                      << (d_result != SAT_VALUE_UNKNOWN)
                      << (d_result != SAT_VALUE_UNKNOWN ? "true" : "false")
                      << std::endl;
    return (d_result != SAT_VALUE_UNKNOWN);
  }

  /** */
  Result getResult() {
    switch(d_result.get()) {
    case SAT_VALUE_TRUE: return Result(Result::SAT);
    case SAT_VALUE_FALSE: return Result(Result::UNSAT);
    case SAT_VALUE_UNKNOWN: return Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    default: Assert(false) << "d_result is garbage";
    }
    return Result();
  }

  /** */
  void setResult(SatValue val) {
    d_result = val;
  }

  // External World helping us help the Strategies

  /**
   * Add a list of assertions from an AssertionPipeline.
   */
  void addAssertions(const preprocessing::AssertionPipeline& assertions);

  // Interface for Strategies to use stuff stored in Decision Engine
  // (which was possibly requested by them on initialization)

  /**
   * Get the assertions. Strategies are notified when these are available.
   */
  AssertionsList& getAssertions() {
    return d_assertions;
  }


  // Interface for Strategies to get information about External World

  bool hasSatLiteral(TNode n) {
    return d_cnfStream->hasLiteral(n);
  }
  SatLiteral getSatLiteral(TNode n) {
    return d_cnfStream->getLiteral(n);
  }
  SatValue getSatValue(SatLiteral l) {
    return d_satSolver->value(l);
  }
  SatValue getSatValue(TNode n) {
    return getSatValue(getSatLiteral(n));
  }
  Node getNode(SatLiteral l) {
    return d_cnfStream->getNode(l);
  }
};/* DecisionEngine class */

}/* CVC4 namespace */

#endif /* CVC4__DECISION__DECISION_ENGINE_H */
