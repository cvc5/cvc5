/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The inference manager for the theory of sets.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__INFERENCE_MANAGER_H
#define CVC4__THEORY__SETS__INFERENCE_MANAGER_H

#include "theory/sets/solver_state.h"
#include "theory/uf/equality_engine.h"

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
class InferenceManager
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  InferenceManager(TheorySetsPrivate& p,
                   SolverState& s,
                   context::Context* c,
                   context::UserContext* u);
  /** reset
   *
   * Called at the beginning of a full effort check. Resets the information
   * related to this class regarding whether facts and lemmas have been
   * processed.
   */
  void reset();
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

  /** Flush lemmas
   *
   * This sends lemmas on the output channel of the theory of sets.
   *
   * The argument preprocess indicates whether preprocessing should be applied
   * (by TheoryEngine) on each of lemmas.
   */
  void flushLemmas(std::vector<Node>& lemmas, bool preprocess = false);
  /** singular version of above */
  void flushLemma(Node lem, bool preprocess = false);
  /** Do we have pending lemmas? */
  bool hasPendingLemmas() const { return !d_pendingLemmas.empty(); }
  /** Applies flushLemmas on d_pendingLemmas */
  void flushPendingLemmas(bool preprocess = false);
  /** flush the splitting lemma ( n OR (NOT n) )
   *
   * If reqPol is not 0, then a phase requirement for n is requested with
   * polarity ( reqPol>0 ).
   */
  void split(Node n, int reqPol = 0);
  /** Have we sent a lemma during the current call to a full effort check? */
  bool hasSentLemma() const;
  /** Have we added a fact during the current call to a full effort check? */
  bool hasAddedFact() const;
  /** Have we processed an inference (fact, lemma, or conflict)? */
  bool hasProcessed() const;
  /** Have we sent lem as a lemma in the current user context? */
  bool hasLemmaCached(Node lem) const;

  /** 
   * Send conflict.
   * @param conf The conflict node to be sent on the output channel
   */
  void conflict(Node conf);

 private:
  /** constants */
  Node d_true;
  Node d_false;
  /** the theory of sets which owns this */
  TheorySetsPrivate& d_parent;
  /** Reference to the state object for the theory of sets */
  SolverState& d_state;
  /** pending lemmas */
  std::vector<Node> d_pendingLemmas;
  /** sent lemma
   *
   * This flag is set to true during a full effort check if this theory
   * called d_out->lemma(...).
   */
  bool d_sentLemma;
  /** added fact
   *
   * This flag is set to true during a full effort check if this theory
   * added an internal fact to its equality engine.
   */
  bool d_addedFact;
  /** A user-context-dependent cache of all lemmas produced */
  NodeSet d_lemmas_produced;
  /**
   * A set of nodes to ref-count. Nodes that are facts or are explanations of
   * facts must be added to this set since the equality engine does not
   * ref count nodes.
   */
  NodeSet d_keep;
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
