/*********************                                                        */
/*! \file decision_engine.h
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

#ifndef __CVC4__DECISION__DECISION_ENGINE_H
#define __CVC4__DECISION__DECISION_ENGINE_H

#include <vector>

#include "decision/decision_strategy.h"

#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/prop_engine.h"
#include "prop/sat_solver_types.h"
#include "util/output.h"

using namespace std;
using namespace CVC4::prop;
using namespace CVC4::decision;

namespace CVC4 {

class DecisionEngine {

  vector <DecisionStrategy* > d_enabledStrategies;
  vector <DecisionStrategy* > d_needSimplifiedPreITEAssertions;

  vector <Node> d_assertions;

  // PropEngine* d_propEngine;
  CnfStream* d_cnfStream;
  DPLLSatSolverInterface* d_satSolver;

  SatValue d_result;

  context::Context* d_satContext;
public:
  // Necessary functions

  /** Constructor, enables decision stragies based on options */
  DecisionEngine(context::Context *c);

  /** Destructor, currently does nothing */
  ~DecisionEngine() {
    Trace("decision") << "Destroying decision engine" << std::endl;
    for(unsigned i = 0; i < d_enabledStrategies.size(); ++i)
      delete d_enabledStrategies[i];
  }
  
  // void setPropEngine(PropEngine* pe) {
  //   // setPropEngine should not be called more than once
  //   Assert(d_propEngine == NULL);
  //   Assert(pe != NULL);
  //   d_propEngine = pe;
  // }

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


  // Interface for External World to use our services

  /** Gets the next decision based on strategies that are enabled */
  SatLiteral getNext(bool &stopSearch) {
    SatLiteral ret = undefSatLiteral;
    for(unsigned i = 0; 
        i < d_enabledStrategies.size() 
          and ret == undefSatLiteral
          and stopSearch == false; ++i) {
      ret = d_enabledStrategies[i]->getNext(stopSearch);
    }
    return ret;
  }

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
    switch(d_result) {
    case SAT_VALUE_TRUE: return Result(Result::SAT);
    case SAT_VALUE_FALSE: return Result(Result::UNSAT);
    case SAT_VALUE_UNKNOWN: return Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    default: Assert(false);
    }
    return Result();
  }

  /** */
  void setResult(SatValue val) {
    d_result = val;
  }

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system.  For now,
   * there's nothing to do here in the DecisionEngine.
   */
  void shutdown() {
    Trace("decision") << "Shutting down decision engine" << std::endl;
  }


  // External World helping us help the Strategies

  /** If one of the enabled strategies needs them  */
  bool needSimplifiedPreITEAssertions() {
    return d_needSimplifiedPreITEAssertions.size() > 0;
  }
  void informSimplifiedPreITEAssertions(const vector<Node> &assertions);

  void addAssertion(Node n);

  // Interface for Strategies to use stuff stored in Decision Engine
  // (which was possibly requested by them on initialization)

  /**
   * Get the assertions. Strategies are notified when these are available. 
   */
  const vector<Node>& getAssertions() {
    return d_assertions;
  }


  // Interface for Strategies to get information about External World

  bool hasSatLiteral(Node n) {
    return d_cnfStream->hasLiteral(n);
  }
  SatLiteral getSatLiteral(Node n) {
    return d_cnfStream->getLiteral(n);
  }
  SatValue getSatValue(SatLiteral l) {
    return d_satSolver->value(l);
  }
  Node getNode(SatLiteral l) {
    return d_cnfStream->getNode(l);
  }

private:
  /**
   * Enable a particular decision strategy, also updating
   * corresponding vector<DecisionStrategy*>-s is the engine
   */
  void enableStrategy(DecisionStrategy* ds);

};/* DecisionEngine class */

}/* CVC4 namespace */

#endif /* __CVC4__DECISION__DECISION_ENGINE_H */
