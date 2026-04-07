/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__SAT_SOLVER_H
#define CVC5__PROP__SAT_SOLVER_H

#include "proof/clause_id.h"
#include "prop/prop_proof_manager.h"
#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace prop {

class SatSolverFactory;
class SatProofManager;
class TheoryProxy;

class SatSolver
{
  friend class SatSolverFactory;

 public:

  /** Virtual destructor */
  virtual ~SatSolver() = default;

  /**
   * Add clause to SAT solver.
   * @param clause    The clause to add.
   * @param removable True to indicate that this clause is not irredundant.
   */
  virtual ClauseId addClause(const SatClause& clause, bool removable) = 0;

  /**
   * Create a new boolean variable in the solver.
   * @param isTheoryAtom is this a theory atom that needs to be asserted to
   * theory
   * @param canErase whether the sat solver can safely eliminate this variable
   */
  virtual SatVariable newVar(bool isTheoryAtom, bool canErase) = 0;

  /**
   * Create a new (or return an existing) boolean variable representing the
   * constant `true`.
   * @return The variable representing true.
   */
  virtual SatVariable trueVar() = 0;

  /**
   * Create a new (or return an existing) boolean variable representing the
   * constant false.
   * @return The variable representing false.
   */
  virtual SatVariable falseVar() = 0;

  /** Check the satisfiability of the added clauses */
  virtual SatValue solve() = 0;

  /** Check the satisfiability of the added clauses */
  virtual SatValue solve(long unsigned int&) = 0;

  /** Check satisfiability under assumptions */
  virtual SatValue solve(const std::vector<SatLiteral>& assumptions) = 0;

  /**
   * Tell SAT solver to only do propagation on next solve().
   *
   * @return true if feature is supported, otherwise false.
   */
  virtual bool setPropagateOnly() { return false; }

  /** Interrupt the solver */
  virtual void interrupt() = 0;

  /** Call value() during the search.*/
  virtual SatValue value(SatLiteral l) = 0;

  /** Call modelValue() when the search is done.*/
  virtual SatValue modelValue(SatLiteral l) = 0;

  /** Check if the solver is in an inconsistent state */
  virtual bool ok() const = 0;

  /**
   * Get list of unsatisfiable assumptions.
   *
   * The returned assumptions are a subset of the assumptions provided to
   * the solve method.
   * Can only be called if satisfiability check under assumptions was used and
   * if it returned SAT_VALUE_FALSE.
   */
  virtual void getUnsatAssumptions(std::vector<SatLiteral>& unsat_assumptions) = 0;

 private:
  /** Is called by the SatSolverFactory right after construction. */
  virtual void initialize() = 0;

};

class CDCLTSatSolver : public SatSolver
{
  friend class SatSolverFactory;

 public:
  /** Virtual destructor */
  ~CDCLTSatSolver() override = default;

  virtual void attachProofManager(PropPfManager* ppm) = 0;

  /** Get the current assertion level */
  virtual uint32_t getAssertionLevel() const = 0;

  virtual void push() = 0;

  virtual void pop() = 0;

  /**
   * Reset the decisions in the DPLL(T) SAT solver at the current assertion
   * level.
   */
  virtual void resetTrail() = 0;

  /**
   * Configure the preferred phase for a decision literal.
   *
   * @note This phase is always enforced when the SAT solver decides to make a
   *       decision on this variable on its own. If a decision is injected into
   *       the SAT solver via TheoryProxy::getNextDecisionRequest(), the
   *       preferred phase will only be considered if the decision was derived
   *       by the decision engine. It will be ignored if the decision was
   *       derived from a theory (the phase enforced by the theory overrides
   *       the preferred phase).
   *
   * @param lit The literal.
   */
  virtual void preferPhase(SatLiteral lit) = 0;

  virtual bool isDecision(SatVariable decn) const = 0;

  /**
   * Return whether variable has a fixed assignment.
   */
  virtual bool isFixed(SatVariable var) const = 0;

  /**
   * Return the current list of decisions made by the SAT solver.
   */
  virtual std::vector<SatLiteral> getDecisions() const = 0;

  /**
   * Return the order heap of the SAT solver, which is a priority queueue
   * of literals ordered with respect to variable activity.
   */
  virtual std::vector<Node> getOrderHeap() const = 0;

  /**
   * Get proof, which is used if option prop-proof-mode is PROOF.
   * @return a complete proof computed by this SAT solver.
   */
  virtual std::shared_ptr<ProofNode> getProof() = 0;

 private:
  /**
   * Regular initialization to generate a solver that does not have
   * CDCLT features. To be called by SatSolverFactory.
   */
  void initialize() override = 0;

  /**
   * Used instead of initialize() to initializes the solver to act as
   * CDCLT solver. To be called by SatSolverFactory.
   */
  virtual void initialize(TheoryProxy* theoryProxy) = 0;

}; /* class CDCLTSatSolver */

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__SAT_SOLVER_H */
