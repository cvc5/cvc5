/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of annotation proof generator utility.
 */

#include "proof/annotation_proof_generator.h"

#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

AnnotationProofGenerator::AnnotationInfo::AnnotationInfo(
    ProofGenerator* pg,
    const std::vector<Node>& args,
    TrustId tid,
    const std::vector<Node>& targs)
    : d_pg(pg), d_args(args), d_tid(tid), d_targs(targs)
{
}

AnnotationProofGenerator::AnnotationProofGenerator(Env& env,
                                                   context::Context* c,
                                                   const std::string& name)
    : EnvObj(env), d_annotations(c ? c : d_env.getUserContext()), d_name(name)
{
}

void AnnotationProofGenerator::addAnnotation(Node fact,
                                             ProofGenerator* pg,
                                             const std::vector<Node>& args,
                                             TrustId tid,
                                             const std::vector<Node>& targs)
{
  Assert(pg != nullptr || tid != TrustId::NONE);
  d_annotations[fact] = std::make_shared<AnnotationInfo>(pg, args, tid, targs);
}

std::shared_ptr<ProofNode> AnnotationProofGenerator::getProofFor(Node fact)
{
  NodeAnnotationInfoMap::const_iterator it = d_annotations.find(fact);
  if (it == d_annotations.end())
  {
    return nullptr;
  }
  const AnnotationInfo& info = *it->second;
  std::shared_ptr<ProofNode> child;
  if (info.d_pg != nullptr)
  {
    child = info.d_pg->getProofFor(fact);
    if (child == nullptr)
    {
      return nullptr;
    }
  }
  else
  {
    ProofNodeManager* pnm = d_env.getProofNodeManager();
    Assert(pnm != nullptr);
    child = pnm->mkTrustedNode(info.d_tid, {}, info.d_targs, fact);
  }
  ProofNodeManager* pnm = d_env.getProofNodeManager();
  Assert(pnm != nullptr);
  return pnm->mkNode(ProofRule::ANNOTATE, {child}, info.d_args, fact);
}

bool AnnotationProofGenerator::hasProofFor(Node fact)
{
  return d_annotations.find(fact) != d_annotations.end();
}

std::string AnnotationProofGenerator::identify() const { return d_name; }

}  // namespace cvc5::internal
