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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__INFERENCE_ID_PROOF_ANNOTATOR_H
#define CVC5__THEORY__INFERENCE_ID_PROOF_ANNOTATOR_H

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "proof/annotation_proof_generator.h"
#include "theory/inference_id.h"

namespace cvc5::internal {
namespace theory {

/** A class that tracks formulas to inference id annotations */
class InferenceIdProofAnnotator : public Annotator
{
  typedef context::CDHashMap<Node, InferenceId> NodeInferenceIdMap;
  typedef context::CDList<std::shared_ptr<ProofNode>> ProofNodeList;

 public:
  InferenceIdProofAnnotator(ProofNodeManager* pnm, context::Context* c);
  /** Set annotation, that formula f should be annotated by id */
  void setAnnotation(Node f, InferenceId id);
  /**
   * Annotate the proof node with the appropriate inference ID. Given proof
   * P proving F that was generated as a lemma with inference id `i`, this
   * returns (ANNOTATION (ANNOTATION P : args i)). The outer ANNOTATION is
   * used since commonly a proof node is "linked" into another, where its
   * children and rule are copied into another. Using ANNOTATION (with no
   * arguments) ensures the top-most ANNOTATION may be linked/copied
   * multiple times; however its child (which counts `i`) will only appear
   * once in the final proof.
   */
  std::shared_ptr<ProofNode> annotate(std::shared_ptr<ProofNode> p) override;

 private:
  /** The proof node manager of the theory */
  ProofNodeManager* d_pnm;
  /** The inference id for each formula */
  NodeInferenceIdMap d_ids;
  /** Ensure we keep proof nodes alive */
  ProofNodeList d_list;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__INFERENCE_ID_PROOF_ANNOTATOR_H */
