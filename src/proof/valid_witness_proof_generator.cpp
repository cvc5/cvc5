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

#include "proof/valid_witness_proof_generator.h"

#include "proof/proof.h"

namespace cvc5::internal {

ValidWitnessProofGenerator::ValidWitnessProofGenerator(Env& env) : EnvObj(env) {}

ValidWitnessProofGenerator::~ValidWitnessProofGenerator() {}

std::shared_ptr<ProofNode> ValidWitnessProofGenerator::getProofFor(Node fact) 
{
  Trace("valid-witness") << "Prove " << fact << std::endl;
  // proofs not yet supported
  CDProof cdp(d_env);
  cdp.addTrustedStep(fact, TrustId::VALID_WITNESS, {}, {});
  return cdp.getProofFor(fact);
}

std::string ValidWitnessProofGenerator::identify() const { return "ValidWitnessProofGenerator"; }

}  // namespace cvc5::internal

