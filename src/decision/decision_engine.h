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

#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"
#include "decision/justification_strategy.h"

namespace CVC4 {

class DecisionEngineOld;

class DecisionEngine
{
 public:
  /** Constructor */
  DecisionEngine(context::Context* sc,
                 context::UserContext* uc,
                 ResourceManager* rm);

  /** Finish initialize */
  void finishInit(prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs);

  /** Gets the next decision based on strategies that are enabled */
  prop::SatLiteral getNext(bool& stopSearch);

  /** Is the DecisionEngine in a state where it has solved everything? */
  bool isDone();

  /**
   * Notify this class that assertion is an (input) assertion, not corresponding
   * to a skolem definition.
   */
  void addAssertion(TNode assertion);
  /**
   * Notify this class that lem is an active assertion in this SAT context
   */
  void notifyRelevantSkolemAssertion(TNode lem);

 private:
  /** Using old */
  bool d_usingOld;
  /** The old implementation */
  std::unique_ptr<DecisionEngineOld> d_decEngineOld;
  /** The new implementation */
  std::unique_ptr<JustificationStrategy> d_jstrat;
  /** Pointer to resource manager for associated SmtEngine */
  ResourceManager* d_resourceManager;

};/* DecisionEngine class */

}/* CVC4 namespace */

#endif /* CVC4__DECISION__DECISION_ENGINE_H */
