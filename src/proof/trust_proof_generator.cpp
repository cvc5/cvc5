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

#include "proof/trust_proof_generator.h"

#include "proof/proof.h"

namespace cvc5::internal {

TrustProofGenerator::TrustProofGenerator(Env& env,
                                         TrustId id,
                                         const std::vector<Node>& args)
    : EnvObj(env), d_tid(id), d_pargs(args)
{
}

TrustProofGenerator::~TrustProofGenerator() {}

std::shared_ptr<ProofNode> TrustProofGenerator::getProofFor(Node fact)
{
  CDProof cdp(d_env);
  cdp.addTrustedStep(fact, d_tid, {}, d_pargs);
  return cdp.getProofFor(fact);
}

std::string TrustProofGenerator::identify() const
{
  return "TrustProofGenerator";
}

}  // namespace cvc5::internal
