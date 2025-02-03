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
 * Valid witness proof generator utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__VALID_WITNESS_PROOF_GENERATOR_H
#define CVC5__PROOF__VALID_WITNESS_PROOF_GENERATOR_H

#include "proof/method_id.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNode;
class ProofNodeManager;

/**
 * Proof generator expected to prove (exists x. P) for all witness terms
 * (witness x. P) introduced.
 */
class ValidWitnessProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment
   */
  ValidWitnessProofGenerator(Env& env);
  virtual ~ValidWitnessProofGenerator();
  /**
   * Get proof for fact.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__VALID_WITNESS_PROOF_GENERATOR_H */
