/*********************                                                        */
/*! \file proof_generator.cpp
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

#include "theory/proof_generator.h"

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

std::shared_ptr<ProofNode> EagerProofGenerator::getProofForConflict(Node conf)
{
  Node ckey = ProofEngineOutputChannel::getConflictKeyValue(conf);
  return getProof(ckey);
}

std::shared_ptr<ProofNode> EagerProofGenerator::getProofForLemma(Node lem)
{
  Node lkey = ProofEngineOutputChannel::getLemmaKeyValue(lem);
  return getProof(lkey);
}

std::shared_ptr<ProofNode> EagerProofGenerator::getProof(Node key)
{
  NodeProofNodeMap::iterator it = d_proofs.find(key);
  if (it == d_proofs.end())
  {
    return nullptr;
  }
  return (*it).second;
}

bool EagerProofGenerator::canProveConflict(Node conf)
{
  Node ckey = ProofEngineOutputChannel::getConflictKeyValue(conf);
  return d_proofs.find(ckey) != d_proofs.end();
}

bool EagerProofGenerator::canProveLemma(Node lem)
{
  Node lkey = ProofEngineOutputChannel::getLemmaKeyValue(lem);
  return d_proofs.find(lkey) != d_proofs.end();
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
