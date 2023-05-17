/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine proof generator.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY_ENGINE_PROOF_GENERATOR_H
#define CVC5__THEORY_ENGINE_PROOF_GENERATOR_H

#include <memory>

#include "context/cdhashmap.h"
#include "context/context.h"
#include "proof/lazy_proof.h"
#include "proof/proof_generator.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

/**
 * A simple proof generator class used by the theory engine. This class
 * stores proofs for TheoryEngine::getExplanation.
 *
 * Notice that this class could be made general purpose. Its main feature is
 * storing lazy proofs for facts in a context-dependent manner.
 */
class TheoryEngineProofGenerator : protected EnvObj, public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<LazyCDProof>>
      NodeLazyCDProofMap;

 public:
  TheoryEngineProofGenerator(Env& env, context::Context* c);
  ~TheoryEngineProofGenerator() {}
  /**
   * Make trust explanation. Called when lpf has a proof of lit from free
   * assumptions in exp.
   *
   * This stores lpf in the map d_proofs below and returns the trust node for
   * this propagation, which has TrustNodeKind TrustNodeKind::PROP_EXP. If this
   * explanation already exists, then the previous explanation is taken, which
   * also suffices for proving the implication.
   */
  TrustNode mkTrustExplain(TNode lit,
                           Node exp,
                           std::shared_ptr<LazyCDProof> lpf);
  /**
   * Get proof for, which expects implications corresponding to explained
   * propagations (=> exp lit) registered by the above method. This currently
   * involves calling the mkScope method of ProofNodeManager internally, which
   * returns a closed proof.
   */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Identify this generator (for debugging, etc..) */
  std::string identify() const override;

 private:
  /** Map from formulas to lazy CD proofs */
  NodeLazyCDProofMap d_proofs;
  /** The false node */
  Node d_false;
};

}  // namespace cvc5::internal

#endif /* CVC5__THEORY_ENGINE_PROOF_GENERATOR_H */
