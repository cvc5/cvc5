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
#include "theory/proof_output_channel.h"

namespace CVC4 {
namespace theory {

ProvenNode::ProvenNode(Node n, ProofGenerator * g) : d_node(n), d_gen(g)
{
  // does not make sense to provide null node with generator
  Assert(d_node.isNull() || d_gen!=nullptr);
  // if a generator is provided, should confirm that it can prove it
  //Assert(d_gen==nullptr || d_gen->canProve(d_node));
}

Node ProvenNode::getNode() const
{
  return d_node;
}

ProofGenerator * ProvenNode::getGenerator() const
{
  return d_gen;
}

bool ProvenNode::isNull() const
{
  return d_node.isNull();
}

ProvenNode ProvenNode::null()
{
  return ProvenNode(Node::null());
}

EagerProofGenerator::EagerProofGenerator(context::UserContext* u,
                                         ProofNodeManager* pnm)
    : d_pnm(pnm), d_proofs(u)
{
}

void EagerProofGenerator::setProofForConflict(Node conf,
                                              std::shared_ptr<ProofNode> pf)
{
  // Normalize based on key
  Node ckey = ProofOutputChannel::getConflictKeyValue(conf);
  d_proofs[ckey] = pf;
}

void EagerProofGenerator::setProofForLemma(Node lem,
                                           std::shared_ptr<ProofNode> pf)
{
  // Normalize based on key
  Node lkey = ProofOutputChannel::getLemmaKeyValue(lem);
  d_proofs[lkey] = pf;
}

std::shared_ptr<ProofNode> EagerProofGenerator::getProofForConflict(Node conf)
{
  Node ckey = ProofOutputChannel::getConflictKeyValue(conf);
  return getProof(ckey);
}

std::shared_ptr<ProofNode> EagerProofGenerator::getProofForLemma(Node lem)
{
  Node lkey = ProofOutputChannel::getLemmaKeyValue(lem);
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

ProvenNode EagerProofGenerator::registerSplit(Node f)
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
  return ProvenNode(lem, this);
}

}  // namespace theory
}  // namespace CVC4
