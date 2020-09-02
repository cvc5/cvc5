/*********************                                                        */
/*! \file inference_manager_buffered.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A buffered inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__INFERENCE_MANAGER_BUFFERED_H
#define CVC4__THEORY__INFERENCE_MANAGER_BUFFERED_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/theory_inference.h"
#include "theory/theory_inference_manager.h"

namespace CVC4 {
namespace theory {

/**
 * The buffered inference manager.  This class implements standard methods
 * for buffering facts, lemmas and phase requirements.
 */
class InferenceManagerBuffered : public TheoryInferenceManager
{
 public:
  InferenceManagerBuffered(Theory& t,
                           TheoryState& state,
                           ProofNodeManager* pnm);
  virtual ~InferenceManagerBuffered() {}
  /**
   * Have we processed an inference during this call to check? In particular,
   * this returns true if we have a pending fact or lemma, or have encountered
   * a conflict.
   */
  bool hasProcessed() const;
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
   */
  void addPendingLemma(Node lem,
                       LemmaProperty p = LemmaProperty::NONE,
                       ProofGenerator* pg = nullptr);
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
   */
  void addPendingFact(Node conc, Node exp, ProofGenerator* pg = nullptr);
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

 protected:
  /** A set of pending inferences to be processed as lemmas */
  std::vector<std::unique_ptr<TheoryInference>> d_pendingLem;
  /** A set of pending inferences to be processed as facts */
  std::vector<std::unique_ptr<TheoryInference>> d_pendingFact;
  /** A map from literals to their pending phase requirement */
  std::map<Node, bool> d_pendingReqPhase;
};

}  // namespace theory
}  // namespace CVC4

#endif
