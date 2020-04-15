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

#include "theory/proof_output_channel.h"

namespace CVC4 {
namespace theory {

EagerProofGenerator::EagerProofGenerator(context::UserContext* u) : d_proofs(u)
{
}

void EagerProofGenerator::setProofForConflict(Node conf,
                                              std::shared_ptr<ProofNode> pf)
{
  // Must normalize to how the call to the output channel's getProof method
  // is intended to be called.
  Node ckey = ProofOutputChannel::getConflictKeyValue(conf);
  d_proofs[ckey] = pf;
}

void EagerProofGenerator::setProofForLemma(Node lem,
                                           std::shared_ptr<ProofNode> pf)
{
  // Must normalize to how the call to the output channel's getProof method
  // is intended to be called.
  Node lkey = ProofOutputChannel::getLemmaKeyValue(lem);
  d_proofs[lkey] = pf;
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

/*
std::shared_ptr<ProofNode> LazyProofGenerator::getProof(Node key)
{

}
*/

}  // namespace theory
}  // namespace CVC4
