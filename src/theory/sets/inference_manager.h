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
 * The inference manager for the theory of sets.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__INFERENCE_MANAGER_H
#define CVC5__THEORY__SETS__INFERENCE_MANAGER_H

#include "theory/inference_manager_buffered.h"
#include "theory/sets/solver_state.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

class TheorySetsPrivate;

/** Inference manager
 *
 * This class manages inferences produced by the theory of sets. It manages
 * whether inferences are processed as external lemmas on the output channel
 * of theory of sets or internally as literals asserted to the equality engine
 * of theory of sets. The latter literals are referred to as "facts".
 */
class InferenceManager : public InferenceManagerBuffered
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  InferenceManager(Env& env, Theory& t, SolverState& s);
  /**
   * Add facts corresponding to ( exp => fact ) via calls to the assertFact
   * method of TheorySetsPrivate.
   *
   * The portions of fact that were unable to be processed as facts are added
   * to the data member d_pendingLemmas.
   *
   * The argument inferType is used for overriding the policy on whether
   * fact is processed as a lemma, where inferType=1 forces fact to be
   * set as a lemma, and inferType=-1 forces fact to be processed as a fact
   * (if possible).
   */
  void assertInference(Node fact,
                       InferenceId id,
                       Node exp,
                       int inferType = 0);
  /** same as above, where exp is interpreted as a conjunction */
  void assertInference(Node fact,
                       InferenceId id,
                       std::vector<Node>& exp,
                       int inferType = 0);
  /** same as above, where conc is interpreted as a conjunction */
  void assertInference(std::vector<Node>& conc,
                       InferenceId id,
                       Node exp,
                       int inferType = 0);
  /** same as above, where both exp and conc are interpreted as conjunctions */
  void assertInference(std::vector<Node>& conc,
                       InferenceId id,
                       std::vector<Node>& exp,
                       int inferType = 0);
  /**
   * Immediately assert an internal fact with the default handling of proofs.
   */
  bool assertSetsFact(Node atom, bool polarity, InferenceId id, Node exp);

  /** flush the splitting lemma ( n OR (NOT n) )
   *
   * If reqPol is not 0, then a phase requirement for n is requested with
   * polarity ( reqPol>0 ).
   */
  void split(Node n, InferenceId id, int reqPol = 0);

 private:
  /** constants */
  Node d_true;
  Node d_false;
  /**
   * Reference to the state object for the theory of sets. We store the
   * (derived) state here, since it has additional methods required in this
   * class.
   */
  SolverState& d_state;
  /** Assert fact recursive
   *
   * This is a helper function for assertInference, which calls assertFact
   * in theory of sets and adds to d_pendingLemmas based on fact.
   * The argument inferType determines the policy on whether fact is processed
   * as a fact or as a lemma (see assertInference above).
   */
  bool assertFactRec(Node fact, InferenceId id, Node exp, int inferType = 0);
};

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__INFERENCE_MANAGER_H */
