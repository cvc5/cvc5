/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

class TheorySetsRewriter;

/**
 * A class that is responsible for proofs for sets theory lemmas. Proofs are
 * constructed lazily when asked for via getProofFor. This class maintains
 * a (user-context-dependent) mapping from formulas that we are responsible
 * for proving and the inference identifier that they correspond to.
 *
 * The main (private) method of this class is convert below, which is
 * called when we need to construct a proof node from an InferInfo.
 */
class InferProofCons : protected EnvObj, public ProofGenerator
{
  typedef context::CDHashMap<Node, InferenceId> NodeInferenceMap;
  typedef context::CDHashMap<Node, Node> NodeExpMap;

 public:
  InferProofCons(Env& env, TheorySetsRewriter* tsr);
  virtual ~InferProofCons() {}

  /**
   * This is called to notify that fact was inferred from exp as a fact with
   * inference identifier id.
   */
  void notifyFact(const Node& conc, const Node& exp, InferenceId id);
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
  /**
   * Main conversion routine. Ensures there is a proof of conc with free
   * assumptions assumps stored in cdp.
   *
   * @param cdp The proof to add to.
   * @param id The inference id of the original lemma or conflict.
   * @param assumps The free assumptions (antecendant) of the inference.
   * @param conc The conclusion of the inference
   * @return true if we successfully added a proof to cdp.
   */
  bool convert(CDProof& cdp,
               InferenceId id,
               const std::vector<Node>& assumps,
               const Node& conc);
  /** The sets rewriter */
  TheorySetsRewriter* d_tsr;
  /** Common constants */
  Node d_false;
  /**
   * Maps lemma formulas to the inference id they were notified with. This is
   * user-context dependent.
   */
  NodeInferenceMap d_uimap;
  /**
   * Maps fact formulas to the inference id they were notified with. This is
   * SAT-context dependent.
   */
  NodeInferenceMap d_fmap;
  /** Maps conclusions to their explanations */
  NodeExpMap d_expMap;
};

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__INFER_PROOF_CONS_H */
