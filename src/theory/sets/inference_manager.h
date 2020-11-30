/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The inference manager for the theory of sets.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__INFERENCE_MANAGER_H
#define CVC4__THEORY__SETS__INFERENCE_MANAGER_H

#include "theory/inference_manager_buffered.h"
#include "theory/sets/solver_state.h"

namespace CVC4 {
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
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  InferenceManager(Theory& t, SolverState& s, ProofNodeManager* pnm);
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
   *
   * The argument c is the name of the inference, which is used for debugging.
   */
  void assertInference(Node fact, Node exp, const char* c, int inferType = 0);
  /** same as above, where exp is interpreted as a conjunction */
  void assertInference(Node fact,
                       std::vector<Node>& exp,
                       const char* c,
                       int inferType = 0);
  /** same as above, where conc is interpreted as a conjunction */
  void assertInference(std::vector<Node>& conc,
                       Node exp,
                       const char* c,
                       int inferType = 0);
  /** same as above, where both exp and conc are interpreted as conjunctions */
  void assertInference(std::vector<Node>& conc,
                       std::vector<Node>& exp,
                       const char* c,
                       int inferType = 0);

  /** flush the splitting lemma ( n OR (NOT n) )
   *
   * If reqPol is not 0, then a phase requirement for n is requested with
   * polarity ( reqPol>0 ).
   */
  void split(Node n, int reqPol = 0);

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
  bool assertFactRec(Node fact, Node exp, int inferType = 0);
};

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SETS__INFERENCE_MANAGER_H */
