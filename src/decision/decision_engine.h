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

#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"

namespace cvc5 {
namespace decision {

class DecisionEngine
{
 public:
  /** Constructor */
  DecisionEngine(context::Context* sc,
                 ResourceManager* rm);
  virtual ~DecisionEngine() {}

  /** Finish initialize */
  void finishInit(prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs);

  /** Presolve, called at the beginning of each check-sat call */
  virtual void presolve() {}

  /**
   * Gets the next decision based on strategies that are enabled. This sets
   * stopSearch to true if no further SAT variables need to be assigned in
   * this SAT context.
   */
  prop::SatLiteral getNext(bool& stopSearch);

  /** Is the DecisionEngine in a state where it has solved everything? */
  virtual bool isDone() = 0;

  /**
   * Notify this class that assertion is an (input) assertion, not corresponding
   * to a skolem definition.
   */
  virtual void addAssertion(TNode assertion) = 0;
  /**
   * Notify this class that lem is the skolem definition for skolem, which is
   * a part of the current assertions.
   */
  virtual void addSkolemDefinition(TNode lem, TNode skolem) = 0;
  /**
   * Notify this class that the literal n has been asserted, possibly
   * propagated by the SAT solver.
   */
  virtual void notifyAsserted(TNode n) {}

 protected:
  /** Get next internal, the engine-specific implementation of getNext */
  virtual prop::SatLiteral getNextInternal(bool& stopSearch) = 0;
  /** Pointer to the SAT context */
  context::Context* d_context;
  /** Pointer to resource manager for associated SmtEngine */
  ResourceManager* d_resourceManager;
  /** Pointer to the CNF stream */
  prop::CnfStream* d_cnfStream;
  /** Pointer to the SAT solver */
  prop::CDCLTSatSolverInterface* d_satSolver;
};

/**
 * Instance of the above class which does nothing. This is used when
 * the decision mode is set to internal.
 */
class DecisionEngineEmpty : public DecisionEngine
{
 public:
  DecisionEngineEmpty(context::Context* sc, ResourceManager* rm);
  bool isDone() override;
  void addAssertion(TNode assertion) override;
  void addSkolemDefinition(TNode lem, TNode skolem) override;

 protected:
  prop::SatLiteral getNextInternal(bool& stopSearch) override;
};

}  // namespace decision
}  // namespace cvc5

#endif /* CVC5__DECISION__DECISION_ENGINE_H */
