/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A buffered inference manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__INFERENCE_MANAGER_BUFFERED_H
#define CVC5__THEORY__INFERENCE_MANAGER_BUFFERED_H

#include "expr/node.h"
#include "theory/theory_inference.h"
#include "theory/theory_inference_manager.h"

namespace cvc5::internal {
namespace theory {

/**
 * The buffered inference manager.  This class implements standard methods
 * for buffering facts, lemmas and phase requirements.
 */
class InferenceManagerBuffered : public TheoryInferenceManager
{
 public:
  InferenceManagerBuffered(Env& env,
                           Theory& t,
                           TheoryState& state,
                           const std::string& statsName,
                           bool cacheLemmas = true);
  virtual ~InferenceManagerBuffered() {}
  /**
   * Do we have a pending fact or lemma?
   */
  bool hasPending() const;
  /**
   * Do we have a pending fact to add as an internal fact to the equality
   * engine?
   */
  bool hasPendingFact() const;
  /** Do we have a pending lemma to send on the output channel? */
  bool hasPendingLemma() const;
  /**
   * Add pending lemma lem with property p, with proof generator pg. If
   * non-null, pg must be able to provide a proof for lem for the remainder
   * of the user context. Pending lemmas are sent to the output channel using
   * doPendingLemmas.
   *
   * @param lem The lemma to send
   * @param id The identifier of the inference
   * @param p The property of the lemma
   * @param pg The proof generator which can provide a proof for lem
   * @param checkCache Whether we want to check that the lemma is already in
   * the cache.
   * @return true if the lemma was added to the list of pending lemmas and
   * false if the lemma is already cached.
   */
  bool addPendingLemma(Node lem,
                       InferenceId id,
                       LemmaProperty p = LemmaProperty::NONE,
                       ProofGenerator* pg = nullptr,
                       bool checkCache = true);
  /**
   * Add pending lemma, where lemma can be a (derived) class of the
   * theory inference base class.
   */
  void addPendingLemma(std::unique_ptr<TheoryInference> lemma);
  /**
   * Add pending fact, which adds a fact on the pending fact queue. It must
   * be the case that:
   * (1) exp => conc is valid,
   * (2) exp is a literal (or conjunction of literals) that holds in the
   * equality engine of the theory.
   *
   * Pending facts are sent to the equality engine of this class using
   * doPendingFacts.
   * @param conc The conclustion
   * @param id The identifier of the inference
   * @param exp The explanation in the equality engine of the theory
   * @param pg The proof generator which can provide a proof for conc
   */
  void addPendingFact(Node conc, InferenceId id, Node exp, ProofGenerator* pg = nullptr);
  /**
   * Add pending fact, where fact can be a (derived) class of the
   * theory inference base class.
   */
  void addPendingFact(std::unique_ptr<TheoryInference> fact);
  /** Add pending phase requirement
   *
   * This method is called to indicate this class should send a phase
   * requirement request to the output channel for literal lit to be
   * decided with polarity pol. The literal lit should be a SAT literal
   * by the time that doPendingPhaseRequirements is called. Typically,
   * lit is a literal that is a subformula of a pending lemma that is processed
   * prior to sending the phase requirement.
   */
  void addPendingPhaseRequirement(Node lit, bool pol);
  /** Do pending facts
   *
   * This method asserts pending facts (d_pendingFact) with explanations
   * to the equality engine of the theory via calls
   * to assertInternalFact.
   *
   * It terminates early if a conflict is encountered, for instance, by
   * equality reasoning within the equality engine.
   *
   * Regardless of whether a conflict is encountered, the vector d_pendingFact
   * is cleared after this call.
   */
  void doPendingFacts();
  /** Do pending lemmas
   *
   * This method send all pending lemmas (d_pendingLem) on the output
   * channel of the theory.
   *
   * Unlike doPendingFacts, this function will not terminate early if a conflict
   * has already been encountered by the theory. The vector d_pendingLem is
   * cleared after this call.
   */
  void doPendingLemmas();
  /**
   * Do pending phase requirements. Calls the output channel for all pending
   * phase requirements and clears d_pendingReqPhase.
   */
  void doPendingPhaseRequirements();
  /** Clear pending facts, lemmas, and phase requirements without processing */
  void clearPending();
  /** Clear pending facts, without processing */
  void clearPendingFacts();
  /** Clear pending lemmas, without processing */
  void clearPendingLemmas();
  /** Clear pending phase requirements, without processing */
  void clearPendingPhaseRequirements();

  /** Returns the number of pending lemmas. */
  std::size_t numPendingLemmas() const;
  /** Returns the number of pending facts. */
  std::size_t numPendingFacts() const;

  /**
   * Send the given theory inference as a lemma on the output channel of this
   * inference manager. This calls TheoryInferenceManager::trustedLemma based
   * on the provided theory inference, and returns true if the lemma was
   * successfully sent.
   */
  bool lemmaTheoryInference(TheoryInference* lem);
  /**
   * Add the given theory inference as an internal fact. This calls
   * TheoryInferenceManager::assertInternalFact based on the provided theory
   * inference.
   */
  void assertInternalFactTheoryInference(TheoryInference* fact);

  /**
   * Notify this inference manager that a conflict was sent in this SAT context.
   * This method is called via TheoryEngine when a conflict is sent. This
   * method will clear all pending facts, lemmas, and phase requirements, as
   * these will be stale after the solver backtracks.
   */
  void notifyInConflict() override;

 protected:
  /** A set of pending inferences to be processed as lemmas */
  std::vector<std::unique_ptr<TheoryInference>> d_pendingLem;
  /** A set of pending inferences to be processed as facts */
  std::vector<std::unique_ptr<TheoryInference>> d_pendingFact;
  /** A map from literals to their pending phase requirement */
  std::map<Node, bool> d_pendingReqPhase;
  /**
   * Whether we are currently processing pending lemmas. This flag ensures
   * that we do not call pending lemmas recursively, which may lead to
   * segfaults.
   */
  bool d_processingPendingLemmas;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif
