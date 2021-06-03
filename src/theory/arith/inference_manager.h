/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Makai Mann
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Customized inference manager for the theory of nonlinear arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__INFERENCE_MANAGER_H
#define CVC5__THEORY__ARITH__INFERENCE_MANAGER_H

#include <vector>

#include "theory/inference_id.h"
#include "theory/inference_manager_buffered.h"

namespace cvc5 {
namespace theory {
namespace arith {

class ArithState;
class TheoryArith;

/**
 * A specialized variant of the InferenceManagerBuffered, tailored to the
 * arithmetic theory.
 *
 * It adds some convenience methods to send ArithLemma and adds a mechanism for
 * waiting lemmas that can be flushed into the pending lemmas of this
 * buffered inference manager.
 * It also extends the caching mechanism of TheoryInferenceManager to cache
 * preprocessing lemmas and non-preprocessing lemmas separately. For the former,
 * it uses the cache provided by the TheoryInferenceManager base class.
 */
class InferenceManager : public InferenceManagerBuffered
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  InferenceManager(TheoryArith& ta, ArithState& astate, ProofNodeManager* pnm);

  /**
   * Add a lemma as pending lemma to this inference manager.
   * If isWaiting is true, the lemma is first stored as waiting lemma and only
   * added as pending lemma when calling flushWaitingLemmas.
   */
  void addPendingLemma(std::unique_ptr<SimpleTheoryLemma> lemma,
                       bool isWaiting = false);
  /**
   * Add a lemma as pending lemma to this inference manager.
   * If isWaiting is true, the lemma is first stored as waiting lemma and only
   * added as pending lemma when calling flushWaitingLemmas.
   */
  void addPendingLemma(const SimpleTheoryLemma& lemma, bool isWaiting = false);
  /**
   * Add a lemma as pending lemma to this inference manager.
   * If isWaiting is true, the lemma is first stored as waiting lemma and only
   * added as pending lemma when calling flushWaitingLemmas.
   */
  void addPendingLemma(const Node& lemma,
                       InferenceId inftype,
                       ProofGenerator* pg = nullptr,
                       bool isWaiting = false,
                       LemmaProperty p = LemmaProperty::NONE);

  /**
   * Flush all waiting lemmas to this inference manager (as pending
   * lemmas). To actually send them, call doPendingLemmas() afterwards.
   */
  void flushWaitingLemmas();

  /**
   * Removes all waiting lemmas without sending them anywhere.
   */
  void clearWaitingLemmas();

  /**
   * Checks whether we have made any progress, that is whether a conflict,
   * lemma or fact was added or whether a lemma or fact is pending.
   */
  bool hasUsed() const;

  /** Checks whether we have waiting lemmas. */
  bool hasWaitingLemma() const;

  /** Returns the number of pending lemmas. */
  std::size_t numWaitingLemmas() const;

  /** Checks whether the given lemma is already present in the cache. */
  virtual bool hasCachedLemma(TNode lem, LemmaProperty p) override;

 protected:
  /**
   * Adds the given lemma to the cache. Returns true if it has not been in the
   * cache yet.
   */
  virtual bool cacheLemma(TNode lem, LemmaProperty p) override;

 private:
  /**
   * Checks whether the lemma is entailed to be false. In this case, it is a
   * conflict.
   */
  bool isEntailedFalse(const SimpleTheoryLemma& lem);

  /** The waiting lemmas. */
  std::vector<std::unique_ptr<SimpleTheoryLemma>> d_waitingLem;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
