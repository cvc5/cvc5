/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference to proof conversion for sets.
 */

#include "theory/sets/infer_proof_cons.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

InferProofCons::InferProofCons(Env& env, context::Context* c) : EnvObj(env) {}

void InferProofCons::notifyFact() {}

std::shared_ptr<ProofNode> InferProofConsgetProofFor(Node fact)
{
  return nullptr;
}

std::string InferProofCons::identify() const { return "sets::InferProofCons"; }

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
