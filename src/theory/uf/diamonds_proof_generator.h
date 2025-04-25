/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Diamonds proof generator utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__DIAMONDS_PROOF_GENERATOR_H
#define CVC5__THEORY__UF__DIAMONDS_PROOF_GENERATOR_H

#include "proof/method_id.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNode;
class ProofNodeManager;

/**
 * Proof generator implementing the "diamonds" preprocessing step, performed
 * by TheoryUF.
 */
class DiamondsProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment
   */
  DiamondsProofGenerator(Env& env);
  virtual ~DiamondsProofGenerator();
  /**
   * Performs ppStaticLearn for theory UF.
   * @param n The asserted formula.
   * @param learned A list of lemmas to add to, if applicable.
   */
  void ppStaticLearn(TNode n, std::vector<TrustNode>& learned);
  /**
   * Get proof for fact. Called on fact that were added to learned by
   * the above method.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__DIAMONDS_PROOF_GENERATOR_H */
