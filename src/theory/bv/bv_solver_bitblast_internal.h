/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blast solver that sends bit-blast lemmas directly to the internal
 * MiniSat.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_BITBLAST_INTERNAL_H
#define CVC5__THEORY__BV__BV_SOLVER_BITBLAST_INTERNAL_H

#include "proof/eager_proof_generator.h"
#include "smt/env_obj.h"
#include "theory/bv/bitblast/proof_bitblaster.h"
#include "theory/bv/bv_solver.h"
#include "theory/bv/proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Bit-blasting solver that sends bit-blasting lemmas directly to the
 * internal MiniSat. It is also ablo to handle atoms of kind
 * BITVECTOR_EAGER_ATOM.
 *
 * Sends lemmas atom <=> bb(atom) to MiniSat on preNotifyFact().
 */
class BVSolverBitblastInternal : public BVSolver
{
 public:
  BVSolverBitblastInternal(Env& env,
                           TheoryState* state,
                           TheoryInferenceManager& inferMgr);
  ~BVSolverBitblastInternal() = default;

  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void preRegisterTerm(TNode n) override {}

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  TrustNode explain(TNode n) override;

  std::string identify() const override { return "BVSolverBitblastInternal"; };

  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  Node getValue(TNode node, bool initialize) override;

  /** get the proof checker of this theory */
  BVProofRuleChecker* getProofChecker();

 private:
  /**
   * Sends a bit-blasting lemma fact <=> d_bitblaster.bbAtom(fact) to the
   * inference manager.
   */
  void addBBLemma(TNode fact);

  /** Bit-blaster used to bit-blast atoms/terms. */
  std::unique_ptr<BBProof> d_bitblaster;
  /** Proof rule checker */
  BVProofRuleChecker d_checker;
  /** Proof generator for unpacking BITVECTOR_EAGER_ATOM. */
  std::unique_ptr<EagerProofGenerator> d_epg;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
