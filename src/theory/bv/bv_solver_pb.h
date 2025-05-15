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

class PseudoBooleanSolver;
class PseudoBooleanBlaster;

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

  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void preRegisterTerm(TNode n) override;

  void postCheck(Theory::Effort level) override;

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  TrustNode explain(TNode n) override;

  std::string identify() const override;

  void computeRelevantTerms(std::set<Node>& termSet) override;

  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  Node getValue(TNode node, bool initialize) override;

 private:
  /** Initialize pseudo-boolean solver. */
  void initPbSolver();

  /** PB solver back end. */
  std::unique_ptr<PseudoBooleanSolver, void (*)(PseudoBooleanSolver*)>
      d_pbSolver;
  /** Bit-blaster used to bit-blast atoms/terms. */
  std::unique_ptr<PseudoBooleanBlaster, void (*)(PseudoBooleanBlaster*)>
      d_pbBlaster;

  /**
   * PB-blast queue for facts sent to this solver.
   * Gets populated on preNotifyFact().
   */
  context::CDQueue<Node> d_facts;

  /**
   * PB-blast list for facts sent to this solver.
   * Used as input for the PB Solver.
   * Gets populated on postCheck().
   */
  context::CDList<Node> d_assumptions;
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
