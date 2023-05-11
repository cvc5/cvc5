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
 * Implementation of the annotation proof generator class.
 */

#include "proof/annotation_proof_generator.h"

#include "proof/proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"

namespace cvc5::internal {

AnnotationProofGenerator::AnnotationProofGenerator(ProofNodeManager* pnm,
                                                   context::Context* c,
                                                   std::string name)
    : d_pnm(pnm),
      d_name(name),
      d_exps(c == nullptr ? &d_context : c),
      d_proofs(c == nullptr ? &d_context : c)
{
}

void AnnotationProofGenerator::setExplanationFor(Node f,
                                                 ProofGenerator* pg,
                                                 Annotator* a)
{
  Assert(pg != nullptr);
  d_exps[f] = std::pair<ProofGenerator*, Annotator*>(pg, a);
}

std::shared_ptr<ProofNode> AnnotationProofGenerator::getProofFor(Node f)
{
  // is the proof already cached?
  NodeProofNodeMap::iterator it = d_proofs.find(f);
  if (it != d_proofs.end())
  {
    return (*it).second;
  }
  // make it into an actual proof now
  NodeExpMap::iterator itx = d_exps.find(f);
  if (itx == d_exps.end())
  {
    return nullptr;
  }
  // get the proof from the proof generator
  std::shared_ptr<ProofNode> pf = itx->second.first->getProofFor(f);
  if (pf == nullptr)
  {
    d_proofs[f] = nullptr;
    return nullptr;
  }
  // now anntoate it if an annotator was provided
  std::shared_ptr<ProofNode> pfa = pf;
  if (itx->second.second != nullptr)
  {
    pfa = itx->second.second->annotate(pf);
  }
  d_proofs[f] = pfa;
  return pfa;
}

TrustNode AnnotationProofGenerator::transform(const TrustNode& trn,
                                              Annotator* a)
{
  setExplanationFor(trn.getProven(), trn.getGenerator(), a);
  return TrustNode::mkReplaceGenTrustNode(trn, this);
}

bool AnnotationProofGenerator::hasProofFor(Node f)
{
  return d_exps.find(f) != d_exps.end();
}

std::string AnnotationProofGenerator::identify() const { return d_name; }

}  // namespace cvc5::internal
