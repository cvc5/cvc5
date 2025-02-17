/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PB-blasting solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_PB_H
#define CVC5__THEORY__BV__BV_SOLVER_PB_H

#include "context/cdqueue.h"
#include "theory/bv/bv_solver.h"

namespace cvc5::internal {

namespace theory {
namespace bv {
namespace pb {

class NotifyResetAssertions;
class BBRegistrar;

/**
 * PB-blasting decision procedure for the theory of bit-vectors.
 *
 * PB-blasting translates bit-vector formulas into equisatisfiable pseudo-
 * Boolean formulas. Building on the concept of bit-blasting, which reduces bit-
 * vector expressions to propositional logic, this technique instead converts
 * bit-vector operations into systems of linear constraints over 0-1 variables.
 *
 * The resulting pseudo-Boolean formulas, expressed as conjunctions of linear
 * inequalities with binary variables, can be solved by pseudo-Boolean solvers
 * (https://simons.berkeley.edu/talks/pseudo-boolean-solving-optimization).
 */
class BVSolverPseudoBoolean : public BVSolver
{
 public:
  BVSolverPseudoBoolean(Env& env,
                        TheoryState* state,
                        TheoryInferenceManager& inferMgr);
  ~BVSolverPseudoBoolean() = default;

  /** TODO(alanctprado): document */
  bool needsEqualityEngine(EeSetupInfo& esi) override;

  /** TODO(alanctprado): document */
  void preRegisterTerm(TNode n) override;

  /** TODO(alanctprado): document */
  void postCheck(Theory::Effort level) override;

  /** TODO(alanctprado): document */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  /** TODO(alanctprado): document */
  TrustNode explain(TNode n) override;

  /** TODO(alanctprado): document */
  std::string identify() const override;

  /** TODO(alanctprado): document */
  void computeRelevantTerms(std::set<Node>& termSet) override;

  /** TODO(alanctprado): document */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  /** TODO(alanctprado): document */
  Node getValue(TNode node, bool initialize) override;

 private:
  /** Initialize pseudo-boolean solver. */
  void initPbSolver();

  /** PB solver back end (configured via options::bvPbSolver). */
  // std::unique_ptr<PseudoBooleanSolver<Node>> d_pbSolver;
  /** Bit-blaster used to bit-blast atoms/terms. */
  // std::unique_ptr<PseudoBooleanBlaster> d_pbBlaster;

  /**
   * TODO(alanctprado): document
   * PB-blast queue for facts sent to this solver.
   * Gets populated on preNotifyFact().
   */
  context::CDQueue<Node> d_facts;

  /**
   * TODO(alanctprado): document
   * PB-blast list for facts sent to this solver.
   * Used as input for the PB Solver.
   * Gets populated on postCheck().
   */
  context::CDList<Node> d_assumptions;

  /** Debugging */
  std::string getTermVariables(TNode term);
  void debugSatisfiedAtom(TNode atom);
  void debugSatisfiedTerm(TNode term);
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
