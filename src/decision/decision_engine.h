/*********************                                                        */
/*! \file decision_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Morgan Deters
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

#include "cvc4_private.h"

#ifndef CVC4__DECISION__DECISION_ENGINE_H
#define CVC4__DECISION__DECISION_ENGINE_H

#include "base/output.h"
#include "context/cdo.h"
#include "decision/decision_strategy.h"
#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"
#include "util/result.h"

namespace CVC4 {

class DecisionEngineOld;

class DecisionEngine {

 public:
  /** Constructor */
  DecisionEngine(context::Context* sc,
                 context::UserContext* uc,
                 ResourceManager* rm);
  /** Finish initialize */
  void finishInit(CDCLTSatSolverInterface* ss, CnfStream* cs);

  /**
   * This is called by SmtEngine, at shutdown time, just before
   * destruction.  It is important because there are destruction
   * ordering issues between some parts of the system.
   */
  void shutdown();

  /** Gets the next decision based on strategies that are enabled */
  SatLiteral getNext(bool& stopSearch);

  /** Is the DecisionEngine in a state where it has solved everything? */
  bool isDone();

  /** */
  //void setResult(SatValue val);

  /**
   * Notify this class that assertion is an (input) assertion, not corresponding
   * to a skolem definition.
   */
  void addAssertion(TNode assertion);
  /**
   * Notify this class  that lem is the skolem definition for skolem, which is
   * a part of the current assertions.
   */
  void addSkolemDefinition(TNode lem, TNode skolem);

  bool hasSatLiteral(TNode n);
  SatLiteral getSatLiteral(TNode n);
  SatValue getSatValue(SatLiteral l);
  SatValue getSatValue(TNode n);
  Node getNode(SatLiteral l);

 private:
  /** Using old */
  bool d_usingOld;
  /** The old implementation */
  std::unique_ptr<DecisionEngineOld> d_decEngineOld;
  /** CNF stream */
  CnfStream* d_cnfStream;
  /** SAT solver */
  CDCLTSatSolverInterface* d_satSolver;
  /** SAT context */
  context::Context* d_satContext;
  /** User context */
  context::UserContext* d_userContext;
  /** Pointer to resource manager for associated SmtEngine */
  ResourceManager* d_resourceManager;

};/* DecisionEngine class */

}/* CVC4 namespace */

#endif /* CVC4__DECISION__DECISION_ENGINE_H */
