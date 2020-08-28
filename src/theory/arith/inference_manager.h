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
#include "theory/arith/nl/inference.h"
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
 * waiting lemmas that can be flushed into the pending lemmas of the underlying
 * buffered inference manager.
 */
class InferenceManager : public InferenceManagerBuffered
{
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  InferenceManager(TheoryArith& ta, ArithState& astate, ProofNodeManager* pnm);

  /** Add a lemma (as pending lemma) to the underlying inference manager. */
  void addLemma(std::shared_ptr<ArithLemma> lemma);
  /** Add a lemma (as pending lemma) to the underlying inference manager. */
  void addLemma(const ArithLemma& lemma);
  /** Add a lemma (as pending lemma) to the underlying inference manager. */
  void addLemma(const Node& lemma, nl::Inference inftype);

  /** Add a lemma (as waiting lemma). */
  void addWaitingLemma(std::shared_ptr<ArithLemma> lemma);
  /** Add a lemma (as waiting lemma). */
  void addWaitingLemma(const ArithLemma& lemma);
  /** Add a lemma (as waiting lemma). */
  void addWaitingLemma(const Node& lemma, nl::Inference inftype);

  /** Flush all waiting lemmas to the underlying inference manager (as pending lemmas). */
  void flushWaitingLemmas();

  /** Add a conflict to the underlying inference manager. */
  void addConflict(const Node& conf, nl::Inference inftype);

  /** Returns the number of pending lemmas. */
  std::size_t countWaitingLemmas() const;
 private:
  /** Checks whether the lemma is not yet in the cache. */
  bool isNewLemma(ArithLemma& lem);
  /**
   * Checks whether the lemma is entailed to be false. In this case, it is a
   * conflict.
   */
  bool isEntailedFalse(const ArithLemma& lem);

  /** The waiting lemmas. */
  std::vector<std::shared_ptr<ArithLemma>> d_waitingLem;

  /** cache of all lemmas sent on the output channel (user-context-dependent) */
  NodeSet d_lemmas;
  /** Same as above, for preprocessed lemmas */
  NodeSet d_lemmasPp;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
