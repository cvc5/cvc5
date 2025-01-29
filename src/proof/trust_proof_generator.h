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
 * Trust proof generator utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__TRUST_PROOF_GENERATOR_H
#define CVC5__PROOF__TRUST_PROOF_GENERATOR_H

#include "proof/method_id.h"
#include "proof/proof_generator.h"
#include "proof/trust_id.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNode;
class ProofNodeManager;

/**
 * This class is used as a (lazy) proof generator for trust steps.
 */
class TrustProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment.
   * @param id The trust id.
   * @param args The proof arguments (if any).
   */
  TrustProofGenerator(Env& env, TrustId id, const std::vector<Node>& args);
  virtual ~TrustProofGenerator();
  /**
   * Get proof for fact. We return a single step proving fact from d_tid.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;

 private:
  /** The trust id */
  TrustId d_tid;
  /** Proof args */
  std::vector<Node> d_pargs;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__TRUST_PROOF_GENERATOR_H */
