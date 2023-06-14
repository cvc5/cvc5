/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The assumption proof generator class.
 */

#include "proof/assumption_proof_generator.h"

#include "proof/proof_node_manager.h"

namespace cvc5::internal {

AssumptionProofGenerator::AssumptionProofGenerator(ProofNodeManager* pnm)
    : d_pnm(pnm)
{
}

std::shared_ptr<ProofNode> AssumptionProofGenerator::getProofFor(Node f)
{
  return d_pnm->mkAssume(f);
}
std::string AssumptionProofGenerator::identify() const
{
  return "AssumptionProofGenerator";
}

}  // namespace cvc5::internal
