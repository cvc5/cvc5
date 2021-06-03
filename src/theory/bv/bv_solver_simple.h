/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple bit-blast solver that sends bit-blast lemmas directly to MiniSat.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_SIMPLE_H
#define CVC5__THEORY__BV__BV_SOLVER_SIMPLE_H

#include "theory/bv/bitblast/proof_bitblaster.h"
#include "theory/bv/bv_solver.h"
#include "theory/bv/proof_checker.h"

namespace cvc5 {

class TConvProofGenerator;

namespace theory {
namespace bv {

/**
 * Simple bit-blasting solver that sends bit-blasting lemmas directly to the
 * internal MiniSat. It is also ablo to handle atoms of kind
 * BITVECTOR_EAGER_ATOM.
 *
 * Sends lemmas atom <=> bb(atom) to MiniSat on preNotifyFact().
 */
class BVSolverSimple : public BVSolver
{
 public:
  BVSolverSimple(TheoryState* state,
                 TheoryInferenceManager& inferMgr,
                 ProofNodeManager* pnm);
  ~BVSolverSimple() = default;

  void preRegisterTerm(TNode n) override {}

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  std::string identify() const override { return "BVSolverSimple"; };

  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  /** get the proof checker of this theory */
  BVProofRuleChecker* getProofChecker();

 private:
  /**
   * Sends a bit-blasting lemma fact <=> d_bitblaster.bbAtom(fact) to the
   * inference manager.
   */
  void addBBLemma(TNode fact);

  /** Proof generator. */
  std::unique_ptr<TConvProofGenerator> d_tcpg;
  /** Bit-blaster used to bit-blast atoms/terms. */
  std::unique_ptr<BBProof> d_bitblaster;
  /** Proof rule checker */
  BVProofRuleChecker d_checker;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

#endif
