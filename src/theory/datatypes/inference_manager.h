/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Datatypes inference manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__INFERENCE_MANAGER_H
#define CVC5__THEORY__DATATYPES__INFERENCE_MANAGER_H

#include "expr/node.h"
#include "theory/datatypes/infer_proof_cons.h"
#include "theory/inference_manager_buffered.h"

namespace cvc5::internal {

class EagerProofGenerator;

namespace theory {
namespace datatypes {

/**
 * The datatypes inference manager, which uses the above class for
 * inferences.
 */
class InferenceManager : public InferenceManagerBuffered
{
  friend class DatatypesInference;

 public:
  InferenceManager(Env& env, Theory& t, TheoryState& state);
  ~InferenceManager();
  /**
   * Add pending inference, which may be processed as either a fact or
   * a lemma based on mustCommunicateFact in DatatypesInference above.
   *
   * @param conc The conclusion of the inference
   * @param exp The explanation of the inference
   * @param id The inference, used for stats and as a hint for constructing
   * the proof of (conc => exp)
   * @param forceLemma Whether this inference *must* be processed as a lemma.
   * Otherwise, it may be processed as a fact or lemma based on
   * mustCommunicateFact.
   */
  void addPendingInference(Node conc,
                           InferenceId id,
                           Node exp,
                           bool forceLemma = false);
  /**
   * Process the current lemmas and facts. This is a custom method that can
   * be seen as overriding the behavior of calling both doPendingLemmas and
   * doPendingFacts. It determines whether facts should be sent as lemmas
   * or processed internally.
   */
  void process();
  /**
   * Send lemma immediately on the output channel
   */
  void sendDtLemma(Node lem,
                   InferenceId id,
                   LemmaProperty p = LemmaProperty::NONE);
  /**
   * Send conflict immediately on the output channel
   */
  void sendDtConflict(const std::vector<Node>& conf, InferenceId id);

 private:
  /**
   * Process datatype inference as a lemma
   */
  TrustNode processDtLemma(Node conc, Node exp, InferenceId id);
  /**
   * Process datatype inference as a fact
   */
  Node processDtFact(Node conc, Node exp, InferenceId id, ProofGenerator*& pg);
  /**
   * Helper function for the above methods. Returns the conclusion, which
   * may be modified so that it is compatible with proofs. If proofs are
   * enabled, it ensures the proof constructor is ready to provide a proof
   * of (=> exp conc).
   *
   * In particular, if conc is a Boolean equality, it is rewritten. This is
   * to ensure that we do not assert equalities of the form (= t true)
   * or (= t false) to the equality engine, which have a reserved internal
   * status for proof generation. If this is not done, then it is possible
   * to have proofs with missing connections and hence free assumptions.
   */
  Node prepareDtInference(Node conc, Node exp, InferenceId id, InferProofCons* ipc);
  /** The false node */
  Node d_false;
  /** The inference to proof converter */
  std::unique_ptr<InferProofCons> d_ipc;
  /** An eager proof generator for lemmas */
  std::unique_ptr<EagerProofGenerator> d_lemPg;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif
