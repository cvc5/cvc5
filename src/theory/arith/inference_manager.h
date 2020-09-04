/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Customized inference manager for the theory of nonlinear arithmetic
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__INFERENCE_MANAGER_H
#define CVC4__THEORY__ARITH__INFERENCE_MANAGER_H

#include <map>
#include <vector>

#include "theory/arith/arith_lemma.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/inference_id.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/inference_manager_buffered.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArith;

/**
 * A specialized variant of the InferenceManagerBuffered, tailored to the
 * arithmetic theory.
 *
 * It adds some convenience methods to send ArithLemma and adds a mechanism for
 * waiting lemmas that can be flushed into the pending lemmas of the this
 * buffered inference manager.
 * It also extends the caching mechanism of TheoryInferenceManager to cache
 * preprocessing lemmas and non-preprocessing lemmas separately. For the former,
 * it uses the cache provided by the TheoryInferenceManager base class.
 */
class InferenceManager : public InferenceManagerBuffered
{
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  InferenceManager(TheoryArith& ta, ArithState& astate, ProofNodeManager* pnm);

  /**
   * Add a lemma as pending lemma to the this inference manager.
   * If isWaiting is true, the lemma is first stored as waiting lemma and only
   * added as pending lemma when calling flushWaitingLemmas.
   */
  void addPendingArithLemma(std::unique_ptr<ArithLemma> lemma,
                            bool isWaiting = false);
  /**
   * Add a lemma as pending lemma to the this inference manager.
   * If isWaiting is true, the lemma is first stored as waiting lemma and only
   * added as pending lemma when calling flushWaitingLemmas.
   */
  void addPendingArithLemma(const ArithLemma& lemma, bool isWaiting = false);
  /**
   * Add a lemma as pending lemma to the this inference manager.
   * If isWaiting is true, the lemma is first stored as waiting lemma and only
   * added as pending lemma when calling flushWaitingLemmas.
   */
  void addPendingArithLemma(const Node& lemma,
                            InferenceId inftype,
                            bool isWaiting = false);

  /**
   * Flush all waiting lemmas to the this inference manager (as pending
   * lemmas). To actually send them, call doPendingLemmas() afterwards.
   */
  void flushWaitingLemmas();

  /** Add a conflict to the this inference manager. */
  void addConflict(const Node& conf, InferenceId inftype);

  /**
   * Checks whether we have made any progress, that is whether a conflict, lemma
   * or fact was added or whether a lemma or fact is pending.
   */
  bool hasUsed() const;

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
  bool isEntailedFalse(const ArithLemma& lem);

  /** The waiting lemmas. */
  std::vector<std::unique_ptr<ArithLemma>> d_waitingLem;

  /** cache of all preprocessed lemmas sent on the output channel
   * (user-context-dependent) */
  NodeSet d_lemmasPp;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
