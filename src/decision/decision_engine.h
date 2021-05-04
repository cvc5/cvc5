/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Andrew Reynolds, Aina Niemetz
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

#include "cvc5_private.h"

#ifndef CVC5__DECISION__DECISION_ENGINE_H
#define CVC5__DECISION__DECISION_ENGINE_H

#include "decision/justification_strategy.h"
#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"

namespace cvc5 {

namespace prop {
class SkolemDefManager;
}

class DecisionEngineOld;

namespace decision {

class DecisionEngine
{
 public:
  /** Constructor */
  DecisionEngine(context::Context* sc,
                 context::UserContext* uc,
                 prop::SkolemDefManager* skdm,
                 ResourceManager* rm);

  /** Finish initialize */
  void finishInit(prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs);

  /** Presolve, called at the beginning of each check-sat call */
  void presolve();

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
   * !!!! temporary until the old justification implementation is deleted.
   * Notify this class  that lem is the skolem definition for skolem, which is
   * a part of the current assertions.
   */
  void addSkolemDefinition(TNode lem, TNode skolem);
  /**
   * Notify this class that the literal n has been asserted, possibly
   * propagated by the SAT solver.
   */
  void notifyAsserted(TNode n);

 private:
  /** The old implementation */
  std::unique_ptr<DecisionEngineOld> d_decEngineOld;
  /** The new implementation */
  std::unique_ptr<JustificationStrategy> d_jstrat;
  /** Pointer to resource manager for associated SmtEngine */
  ResourceManager* d_resourceManager;
  /** using old implementation? */
  bool d_useOld;
};

}  // namespace decision
}  // namespace cvc5

#endif /* CVC5__DECISION__DECISION_ENGINE_H */
