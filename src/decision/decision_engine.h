/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace decision {

class DecisionEngine : protected EnvObj
{
 public:
  /** Constructor */
  DecisionEngine(Env& env, prop::CDCLTSatSolver* ss, prop::CnfStream* cs);
  virtual ~DecisionEngine() {}

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
   * If skolem is null, notify this class that assertion is an (input)
   * assertion, not corresponding to a skolem definition.
   *
   * If skolem is non-null, notify this class that lem is the skolem definition
   * for skolem, which is a part of the current assertions.
   */
  virtual void addAssertion(TNode lem, TNode skolem, bool isLemma) = 0;
  /**
   * Notify this class that the list of lemmas defs are now active in the
   * current SAT context.
   */
  virtual void notifyActiveSkolemDefs(std::vector<TNode>& defs) {}
  /**
   * Track active skolem defs, whether we need to call the above method
   * when appropriate.
   */
  virtual bool needsActiveSkolemDefs() const { return false; }

 protected:
  /** Get next internal, the engine-specific implementation of getNext */
  virtual prop::SatLiteral getNextInternal(bool& stopSearch) = 0;
  /** Pointer to the SAT solver */
  prop::CDCLTSatSolver* d_satSolver;
  /** Pointer to the CNF stream */
  prop::CnfStream* d_cnfStream;
};

/**
 * Instance of the above class which does nothing. This is used when
 * the decision mode is set to internal.
 */
class DecisionEngineEmpty : public DecisionEngine
{
 public:
  DecisionEngineEmpty(Env& env);
  bool isDone() override;
  void addAssertion(TNode lem, TNode skolem, bool isLemma) override;

 protected:
  prop::SatLiteral getNextInternal(bool& stopSearch) override;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__DECISION_ENGINE_H */
