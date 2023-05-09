/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The inference manager for the theory of bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__INFERENCE_MANAGER_H
#define CVC5__THEORY__BAGS__INFERENCE_MANAGER_H

#include "theory/inference_manager_buffered.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

class SolverState;

/** Inference manager
 *
 * This class manages inferences produced by the theory of bags. It manages
 * whether inferences are processed as external lemmas on the output channel
 * of theory of bags or internally as literals asserted to the equality engine
 * of theory of bags. The latter literals are referred to as "facts".
 */
class InferenceManager : public InferenceManagerBuffered
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  InferenceManager(Env& env, Theory& t, SolverState& s);

  /**
   * Do pending method. This processes all pending facts, lemmas and pending
   * phase requests based on the policy of this manager. This means that
   * we process the pending facts first and abort if in conflict. Otherwise, we
   * process the pending lemmas and then the pending phase requirements.
   * Notice that we process the pending lemmas even if there were facts.
   */
  // TODO issue #78: refactor this with theory of strings
  void doPending();

 private:
  /** constants */
  Node d_true;
  Node d_false;
  /**
   * Reference to the state object for the theory of bags. We store the
   * (derived) state here, since it has additional methods required in this
   * class.
   */
  SolverState& d_state;
};

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__INFERENCE_MANAGER_H */
