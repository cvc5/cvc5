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
 * The inference id annotator class.
 */

#include "theory/inference_id_proof_annotator.h"

#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"

namespace cvc5::internal {
namespace theory {

InferenceIdProofAnnotator::InferenceIdProofAnnotator(ProofNodeManager* pnm,
                                                     context::Context* c)
    : d_pnm(pnm), d_ids(c), d_list(c)
{
}
void InferenceIdProofAnnotator::setAnnotation(Node f, InferenceId id)
{
  d_ids[f] = id;
}

std::shared_ptr<ProofNode> InferenceIdProofAnnotator::annotate(
    std::shared_ptr<ProofNode> p)
{
  Node f = p->getResult();
  NodeInferenceIdMap::iterator it = d_ids.find(f);
  if (it != d_ids.end())
  {
    std::vector<Node> pfArgs;
    pfArgs.push_back(mkInferenceIdNode(it->second));
    std::shared_ptr<ProofNode> pa =
        d_pnm->mkNode(PfRule::ANNOTATION, {p}, pfArgs);
    // for now, do a double annotation to make stats accurate
    std::shared_ptr<ProofNode> paf =
        d_pnm->mkNode(PfRule::ANNOTATION, {pa}, {});
    d_list.push_back(paf);
    return paf;
  }
  return p;
}

}  // namespace theory
}  // namespace cvc5::internal
