/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the abstract proof generator class.
 */

#include "proof/eager_proof_generator.h"

#include "proof/proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

EagerProofGenerator::EagerProofGenerator(Env& env,
                                         context::Context* c,
                                         std::string name)
    : EnvObj(env), d_name(name), d_proofs(c == nullptr ? &d_context : c)
{
}

void EagerProofGenerator::setProofFor(Node f, std::shared_ptr<ProofNode> pf)
{
  // pf should prove f
  Assert(pf->getResult() == f)
      << "EagerProofGenerator::setProofFor: unexpected result" << std::endl
      << "Expected: " << f << std::endl
      << "Actual: " << pf->getResult() << std::endl;
  d_proofs[f] = pf;
}
void EagerProofGenerator::setProofForConflict(Node conf,
                                              std::shared_ptr<ProofNode> pf)
{
  // Normalize based on key
  Node ckey = TrustNode::getConflictProven(conf);
  setProofFor(ckey, pf);
}

void EagerProofGenerator::setProofForLemma(Node lem,
                                           std::shared_ptr<ProofNode> pf)
{
  // Normalize based on key
  Node lkey = TrustNode::getLemmaProven(lem);
  setProofFor(lkey, pf);
}

void EagerProofGenerator::setProofForPropExp(TNode lit,
                                             Node exp,
                                             std::shared_ptr<ProofNode> pf)
{
  // Normalize based on key
  Node pekey = TrustNode::getPropExpProven(lit, exp);
  setProofFor(pekey, pf);
}

std::shared_ptr<ProofNode> EagerProofGenerator::getProofFor(Node f)
{
  NodeProofNodeMap::iterator it = d_proofs.find(f);
  if (it == d_proofs.end())
  {
    return nullptr;
  }
  return (*it).second;
}

bool EagerProofGenerator::hasProofFor(Node f)
{
  return d_proofs.find(f) != d_proofs.end();
}

TrustNode EagerProofGenerator::mkTrustNode(Node n,
                                           std::shared_ptr<ProofNode> pf,
                                           bool isConflict)
{
  if (pf == nullptr)
  {
    return TrustNode::null();
  }
  if (isConflict)
  {
    // this shouldnt modify the key
    setProofForConflict(n, pf);
    // we can now return the trust node
    return TrustNode::mkTrustConflict(n, this);
  }
  // this shouldnt modify the key
  setProofForLemma(n, pf);
  // we can now return the trust node
  return TrustNode::mkTrustLemma(n, this);
}

TrustNode EagerProofGenerator::mkTrustNode(Node conc,
                                           PfRule id,
                                           const std::vector<Node>& exp,
                                           const std::vector<Node>& args,
                                           bool isConflict)
{
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  // if no children, its easy
  if (exp.empty())
  {
    // do not use "conc" as expected here, instead this will be checked
    // later in setProofFor, where conc may be negated if isConflict is true
    std::shared_ptr<ProofNode> pf = pnm->mkNode(id, {}, args);
    return mkTrustNode(conc, pf, isConflict);
  }
  // otherwise, we use CDProof + SCOPE
  CDProof cdp(d_env);
  cdp.addStep(conc, id, exp, args);
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(conc);
  // We use mkNode instead of mkScope, since there is no reason to check
  // whether the free assumptions of pf are in exp, since they are by the
  // construction above.
  std::shared_ptr<ProofNode> pfs = pnm->mkNode(PfRule::SCOPE, {pf}, exp);
  return mkTrustNode(pfs->getResult(), pfs, isConflict);
}

TrustNode EagerProofGenerator::mkTrustedRewrite(Node a,
                                                Node b,
                                                std::shared_ptr<ProofNode> pf)
{
  if (pf == nullptr)
  {
    return TrustNode::null();
  }
  Node eq = a.eqNode(b);
  setProofFor(eq, pf);
  return TrustNode::mkTrustRewrite(a, b, this);
}

TrustNode EagerProofGenerator::mkTrustedRewrite(Node a,
                                                Node b,
                                                PfRule id,
                                                const std::vector<Node>& args)
{
  Node eq = a.eqNode(b);
  CDProof cdp(d_env);
  cdp.addStep(eq, id, {}, args);
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(eq);
  return mkTrustedRewrite(a, b, pf);
}

TrustNode EagerProofGenerator::mkTrustedPropagation(
    Node n, Node exp, std::shared_ptr<ProofNode> pf)
{
  if (pf == nullptr)
  {
    return TrustNode::null();
  }
  setProofForPropExp(n, exp, pf);
  return TrustNode::mkTrustPropExp(n, exp, this);
}

TrustNode EagerProofGenerator::mkTrustNodeSplit(Node f)
{
  // make the lemma
  Node lem = f.orNode(f.notNode());
  return mkTrustNode(lem, PfRule::SPLIT, {}, {f}, false);
}

std::string EagerProofGenerator::identify() const { return d_name; }

}  // namespace cvc5::internal
