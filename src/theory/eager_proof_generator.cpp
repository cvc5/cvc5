/*********************                                                        */
/*! \file eager_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the abstract proof generator class
 **/

#include "theory/eager_proof_generator.h"

#include "expr/proof_node_manager.h"
#include "theory/proof_engine_output_channel.h"

namespace CVC4 {
namespace theory {

EagerProofGenerator::EagerProofGenerator(context::UserContext* u,
                                         ProofNodeManager* pnm)
    : d_pnm(pnm), d_proofs(u)
{
}

void EagerProofGenerator::setProofForConflict(Node conf,
                                              std::shared_ptr<ProofNode> pf)
{
  // Normalize based on key
  Node ckey = ProofEngineOutputChannel::getConflictKeyValue(conf);
  d_proofs[ckey] = pf;
}

void EagerProofGenerator::setProofForLemma(Node lem,
                                           std::shared_ptr<ProofNode> pf)
{
  // Normalize based on key
  Node lkey = ProofEngineOutputChannel::getLemmaKeyValue(lem);
  d_proofs[lkey] = pf;
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

TrustNode EagerProofGenerator::mkTrustNode( Node n, std::shared_ptr<ProofNode> pf)
{
  if (pf==nullptr)
  {
    return TrustNode::null();
  }
  // this shouldnt modify the key
  setProofForLemma(n, pf);
  // we can now return the trust node
  return TrustNode::mkTrustLemma(n, this);
}

TrustNode EagerProofGenerator::mkTrustNode(Node n, PfRule id, const std::vector<Node>& args)
{
  std::vector<std::shared_ptr<ProofNode>> children;
  std::shared_ptr<ProofNode> pf = d_pnm->mkNode(id, children, args, n);
  return mkTrustNode(n, pf);
}

TrustNode EagerProofGenerator::assertSplit(Node f)
{
  // make the lemma
  Node lem = f.orNode(f.notNode());
  // construct a proof for it
  std::vector<std::shared_ptr<ProofNode>> children;
  std::vector<Node> args;
  args.push_back(f);
  std::shared_ptr<ProofNode> p =
      d_pnm->mkNode(PfRule::SPLIT, children, args, lem);
  // store the mapping
  setProofForLemma(lem, p);
  // return the lemma
  return TrustNode::mkTrustLemma(lem, this);
}

}  // namespace theory
}  // namespace CVC4
