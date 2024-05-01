/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference to proof conversion for sets.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__INFER_PROOF_CONS_H
#define CVC5__THEORY__SETS__INFER_PROOF_CONS_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

/**
 *
 * The main (private) method of this class is convert below, which is
 * called when we need to construct a proof node from an InferInfo.
 */
class InferProofCons : protected EnvObj, public ProofGenerator
{
  typedef context::CDHashMap<Node, InferenceId> NodeInferenceMap;

 public:
  InferProofCons(Env& env, context::Context* c);
  virtual ~InferProofCons() {}

  /**
   * This is called to notify that conf was called as a conflict with inference
   * identifier id.
   */
  void notifyConflict(const Node& conf, InferenceId id);
  /**
   * This is called to notify that conf was called as a lemma with inference
   * identifier id.
   */
  void notifyLemma(const Node& lem, InferenceId id);

  /**
   * This returns the proof for fact. This is required for using this class as
   * a lazy proof generator.
   *
   * It should be the case that a call was made to notifyConflict or
   * notifyLemma was called on fact.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** Identify this generator (for debugging, etc..) */
  virtual std::string identify() const override;

 private:
  bool convert(CDProof& cdp,
               InferenceId id,
               const std::vector<Node>& assumps,
               const Node& conc);
  /** Common constants */
  Node d_tid;
  Node d_false;
  /** Maps formulas to the inference id they were notified with */
  NodeInferenceMap d_imap;
};

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__INFER_PROOF_CONS_H */
