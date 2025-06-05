/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite proof generator utility.
 */

#include "proof/rewrite_proof_generator.h"

#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

RewriteProofGenerator::RewriteProofGenerator(Env& env, MethodId id)
    : EnvObj(env), ProofGenerator(), d_id(id)
{
  // initialize the proof args
  addMethodIds(nodeManager(),
               d_pargs,
               MethodId::SB_DEFAULT,
               MethodId::SBA_SEQUENTIAL,
               d_id);
}
RewriteProofGenerator::~RewriteProofGenerator() {}

std::shared_ptr<ProofNode> RewriteProofGenerator::getProofFor(Node fact)
{
  if (fact.getKind() != Kind::EQUAL)
  {
    Assert(false) << "Expected an equality in RewriteProofGenerator, got "
                  << fact;
    return nullptr;
  }
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  const Node& t = fact[0];
  Node tp = d_env.rewriteViaMethod(t, d_id);
  if (tp != fact[1])
  {
    Assert(false) << "Could not prove " << fact << " via RewriteProofGenerator";
    return nullptr;
  }
  std::vector<Node> pargs{t};
  pargs.insert(pargs.end(), d_pargs.begin(), d_pargs.end());
  std::shared_ptr<ProofNode> pf =
      pnm->mkNode(ProofRule::MACRO_SR_EQ_INTRO, {}, pargs, fact);
  return pf;
}

std::string RewriteProofGenerator::identify() const
{
  return "RewriteProofGenerator";
}

}  // namespace cvc5::internal
