/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitblast proof generator for generating bit-blast proof steps.
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__BITBLAST_PROOF_GENERATOR_H
#define CVC5__THEORY__BV__BITBLAST__BITBLAST_PROOF_GENERATOR_H

#include "proof/proof_generator.h"
#include "proof/proof_node_manager.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class TConvProofGenerator;

namespace theory {
namespace bv {

/** Proof generator fot bit-blast proofs. */
class BitblastProofGenerator : public ProofGenerator, protected EnvObj
{
 public:
  BitblastProofGenerator(Env& env,
                         TConvProofGenerator* tcpg);
  ~BitblastProofGenerator(){};

  /**
   * Get proof for, which expects an equality of the form t = bb(t).
   * This returns a proof based on the term conversion proof generator utility.
   */
  std::shared_ptr<ProofNode> getProofFor(Node eq) override;

  std::string identify() const override { return "BitblastStepProofGenerator"; }

  /**
   * Record bit-blast step for bit-vector atom t.
   *
   * @param t Bit-vector atom
   * @param bbt The bit-blasted term obtained from bit-blasting t without
   *            applying any rewriting.
   * @param eq The equality that needs to be justified,
   *           i.e.,t = rewrite(bb(rewrite(t)))
   */
  void addBitblastStep(TNode t, TNode bbt, TNode eq);

 private:
  /**
   * The associated term conversion proof generator, which tracks the
   * individual bit-blast steps.
   */
  TConvProofGenerator* d_tcpg;

  /**
   * Cache that maps equalities to information required to reconstruct the
   * proof for given equality.
   */
  std::unordered_map<Node, std::tuple<Node, Node>> d_cache;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
#endif
