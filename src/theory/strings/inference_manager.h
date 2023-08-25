/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Customized inference manager for the theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__INFERENCE_MANAGER_H
#define CVC5__THEORY__STRINGS__INFERENCE_MANAGER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "context/context.h"
#include "expr/node.h"
#include "proof/proof_node_manager.h"
#include "theory/ext_theory.h"
#include "theory/inference_manager_buffered.h"
#include "theory/output_channel.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/infer_proof_cons.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"
#include "theory/theory_inference_manager.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/** Inference Manager
 *
 * The purpose of this class is to process inference steps for strategies
 * in the theory of strings.
 *
 * In particular, inferences are given to this class via calls to functions:
 *
 * sendInternalInference, sendInference, sendSplit
 *
 * This class decides how the conclusion of these calls will be processed.
 * It primarily has to decide whether the conclusions will be processed:
 *
 * (1) Internally in the strings solver, via calls to equality engine's
 * assertLiteral and assertPredicate commands. We refer to these literals as
 * "facts",
 * (2) Externally on the output channel of theory of strings as "lemmas",
 * (3) External on the output channel as "conflicts" (when a conclusion of an
 * inference is false).
 *
 * It buffers facts and lemmas in vectors d_pending and d_pending_lem
 * respectively.
 *
 * When applicable, facts can be flushed to the equality engine via a call to
 * doPendingFacts, and lemmas can be flushed to the output channel via a call
 * to doPendingLemmas.
 *
 * It also manages other kinds of interaction with the output channel of the
 * theory of strings, e.g. sendPhaseRequirement, setModelUnsound, and
 * with the extended theory object e.g. markCongruent.
 */
class InferenceManager : public InferenceManagerBuffered
{
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, Node> NodeNodeMap;
  friend class InferInfo;

 public:
  InferenceManager(Env& env,
                   Theory& t,
                   SolverState& s,
                   TermRegistry& tr,
                   ExtTheory& e,
                   SequencesStatistics& statistics);
  ~InferenceManager() {}

  /**
   * Do pending method. This processes all pending facts, lemmas and pending
   * phase requests based on the policy of this manager. This means that
   * we process the pending facts first and abort if in conflict. Otherwise, we
   * process the pending lemmas and then the pending phase requirements.
   * Notice that we process the pending lemmas even if there were facts.
   */
  void doPending();

  /** send internal inferences
   *
   * This is called when we have inferred exp => conc, where exp is a set
   * of equalities and disequalities that hold in the current equality engine.
   * This method adds equalities and disequalities ~( s = t ) via
   * sendInference such that both s and t are either constants or terms
   * that already occur in the equality engine, and ~( s = t ) is a consequence
   * of conc. This function can be seen as a "conservative" version of
   * sendInference below in that it does not introduce any new non-constant
   * terms to the state.
   *
   * The argument infer identifies the reason for the inference.
   * This is used for debugging and statistics purposes.
   *
   * Return true if the inference is complete, in the sense that we infer
   * inferences that are equivalent to conc. This returns false e.g. if conc
   * (or one of its conjuncts if it is a conjunction) was not inferred due
   * to the criteria mentioned above.
   */
  bool sendInternalInference(std::vector<Node>& exp,
                             Node conc,
                             InferenceId infer);

  /** send inference
   *
   * This function should be called when exp => eq. The set exp
   * contains literals that are explainable, i.e. those that hold in the
   * equality engine of the theory of strings. On the other hand, the set
   * noExplain contains nodes that are not explainable by the theory of strings.
   * This method may call sendLemma or otherwise add a InferInfo to d_pending,
   * indicating a fact should be asserted to the equality engine. Overall, the
   * result of this method is one of the following:
   *
   * [1] (No-op) Do nothing if eq is equivalent to true,
   *
   * [2] (Infer) Indicate that eq should be added to the equality engine of this
   * class with explanation exp, where exp is a set of literals that currently
   * hold in the equality engine. We add this to the pending vector d_pending.
   *
   * [3] (Lemma) Indicate that the lemma
   *   ( EXPLAIN(exp \ noExplain) ^ noExplain ) => eq
   * should be sent on the output channel of the theory of strings, where
   * EXPLAIN returns the explanation of the node in exp in terms of the literals
   * asserted to the theory of strings, as computed by the equality engine.
   * This is also added to a pending vector, d_pendingLem.
   *
   * [4] (Conflict) Immediately report a conflict EXPLAIN(exp) on the output
   * channel of the theory of strings.
   *
   * Determining which case to apply depends on the form of eq and whether
   * noExplain is empty. In particular, lemmas must be used whenever noExplain
   * is non-empty, conflicts are used when noExplain is empty and eq is false.
   *
   * @param exp The explanation of eq.
   * @param noExplain The subset of exp that cannot be explained by the
   * equality engine. This may impact whether we are processing this call as a
   * fact or as a lemma.
   * @param eq The conclusion.
   * @param infer Identifies the reason for inference, used for
   * debugging. This updates the statistics about the number of inferences made
   * of each type.
   * @param isRev Whether this is the "reverse variant" of the inference, which
   * is used as a hint for proof reconstruction.
   * @param asLemma If true, then this method will send a lemma instead
   * of a fact whenever applicable.
   * @return true if the inference was not trivial (e.g. its conclusion did
   * not rewrite to true).
   */
  bool sendInference(const std::vector<Node>& exp,
                     const std::vector<Node>& noExplain,
                     Node eq,
                     InferenceId infer,
                     bool isRev = false,
                     bool asLemma = false);
  /** same as above, but where noExplain is empty */
  bool sendInference(const std::vector<Node>& exp,
                     Node eq,
                     InferenceId infer,
                     bool isRev = false,
                     bool asLemma = false);

  /** Send inference
   *
   * This implements the above methods for the InferInfo object. It is called
   * by the methods above.
   *
   * The inference info ii should have a rewritten conclusion and should not be
   * trivial (InferInfo::isTrivial). It is the responsibility of the caller to
   * ensure this.
   *
   * If the flag asLemma is true, then this method will send a lemma instead
   * of a fact whenever applicable.
   */
  void sendInference(InferInfo& ii, bool asLemma = false);
  /** Send split
   *
   * This requests that ( a = b V a != b ) is sent on the output channel as a
   * lemma. We additionally request a phase requirement for the equality a=b
   * with polarity preq.
   *
   * The argument infer identifies the reason for inference, used for
   * debugging. This updates the statistics about the number of
   * inferences made of each type.
   *
   * This method returns true if the split was non-trivial, and false
   * otherwise. A split is trivial if a=b rewrites to a constant.
   */
  bool sendSplit(Node a, Node b, InferenceId infer, bool preq = true);

  //----------------------------constructing antecedants
  /**
   * Adds equality a = b to the vector exp if a and b are distinct terms. It
   * must be the case that areEqual( a, b ) holds in this context.
   */
  void addToExplanation(Node a, Node b, std::vector<Node>& exp) const;
  /** Adds lit to the vector exp if it is non-null */
  void addToExplanation(Node lit, std::vector<Node>& exp) const;
  //----------------------------end constructing antecedants
  /**
   * Have we processed an inference during this call to check? In particular,
   * this returns true if we have a pending fact or lemma, or have encountered
   * a conflict.
   */
  bool hasProcessed() const;

  // ------------------------------------------------- extended theory
  /**
   * Mark that extended function is inactive. If contextDepend is true,
   * then this mark is SAT-context dependent, otherwise it is user-context
   * dependent (see ExtTheory::markInactive).
   */
  void markInactive(Node n, ExtReducedId id, bool contextDepend = true);
  // ------------------------------------------------- end extended theory

  /**
   * Called when ii is ready to be processed as a conflict. This makes a
   * trusted node whose generator is the underlying proof equality engine
   * (if it exists), and sends it on the output channel.
   */
  void processConflict(const InferInfo& ii);

 private:
  /** Called when ii is ready to be processed as a fact */
  void processFact(InferInfo& ii, ProofGenerator*& pg);
  /** Called when ii is ready to be processed as a lemma */
  TrustNode processLemma(InferInfo& ii, LemmaProperty& p);
  /**
   * min prefix explain
   *
   * @param x A string term
   * @param prefix The prefix (suffix).
   * @param assumptions The set of assumptions we are minimizing
   * @param emap The explanation map for assumptions (getExplanationMap).
   * @param isSuf Whether prefix denotes a suffix
   * @return A subset of assumptions that imply x does not have the given
   * prefix.
   */
  Node mkPrefixExplainMin(Node x,
                          Node prefix,
                          const std::vector<TNode>& assumptions,
                          const std::map<TNode, TNode>& emap,
                          bool isSuf = false);
  /**
   * Returns a mapping from terms to equalities, where t -> E if E is an
   * equality of the form (= t *) or (= * t) from assumptions.
   */
  static std::map<TNode, TNode> getExplanationMap(
      const std::vector<TNode>& assumptions);
  /** Reference to the solver state of the theory of strings. */
  SolverState& d_state;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** the extended theory object for the theory of strings */
  ExtTheory& d_extt;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /** Conversion from inferences to proofs for facts */
  std::unique_ptr<InferProofCons> d_ipc;
  /**
   * Conversion from inferences to proofs for lemmas and conflicts. This is
   * separate from the above proof generator to avoid rare cases where the
   * conclusion of a lemma is a duplicate of the conclusion of another lemma,
   * or is a fact in the current equality engine.
   */
  std::unique_ptr<InferProofCons> d_ipcl;
  /** Common constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif
