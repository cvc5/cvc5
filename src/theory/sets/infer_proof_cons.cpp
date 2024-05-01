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

InferProofCons::InferProofCons(Env& env, context::Context* c) : EnvObj(env), d_imap(userContext()) {}

void InferProofCons::notifyConflict(const Node& conf, InferenceId id)
{
  d_imap[conf.notNode()] = id;
}

void InferProofCons::notifyLemma(const Node& lem, InferenceId id)
{
  d_imap[lem] = id;
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  Trace("sets-ipc") << "Get proof for " << fact << "..." << std::endl;
  NodeInferenceMap::iterator it = d_imap.find(fact);
  if (it==d_imap.end())
  {
    return nullptr;
  }
  InferenceId id = it->second;
  Trace("sets-ipc") << "...inference identifier was " << id << std::endl;

  return nullptr;
}

std::string InferProofCons::identify() const { return "sets::InferProofCons"; }

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
