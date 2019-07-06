/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Customized inference manager for the theory of strings
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__INFERENCE_MANAGER_H
#define CVC4__THEORY__STRINGS__INFERENCE_MANAGER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace strings {

class TheoryStrings;

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
 * theory of strings, e.g. sendPhaseRequirement.
 */
class InferenceManager
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  InferenceManager(TheoryStrings& p,
                   context::Context* c,
                   context::UserContext* u,
                   eq::EqualityEngine& ee,
                   OutputChannel& out);
  ~InferenceManager() {}

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
   * The argument c is a string identifying the reason for the inference.
   * This string is used for debugging purposes.
   *
   * Return true if the inference is complete, in the sense that we infer
   * inferences that are equivalent to conc. This returns false e.g. if conc
   * (or one of its conjuncts if it is a conjunction) was not inferred due
   * to the criteria mentioned above.
   */
  bool sendInternalInference(std::vector<Node>& exp, Node conc, const char* c);
  /** send inference
   *
   * This function should be called when ( exp ^ exp_n ) => eq. The set exp
   * contains literals that are explainable, i.e. those that hold in the
   * equality engine of the theory of strings. On the other hand, the set
   * exp_n ("explanations new") contain nodes that are not explainable by the
   * theory of strings. This method may call sendInfer or sendLemma. Overall,
   * the result of this method is one of the following:
   *
   * [1] (No-op) Do nothing if eq is true,
   *
   * [2] (Infer) Indicate that eq should be added to the equality engine of this
   * class with explanation EXPLAIN(exp), where EXPLAIN returns the
   * explanation of the node in exp in terms of the literals asserted to the
   * theory of strings,
   *
   * [3] (Lemma) Indicate that the lemma ( EXPLAIN(exp) ^ exp_n ) => eq should
   * be sent on the output channel of the theory of strings, or
   *
   * [4] (Conflict) Immediately report a conflict EXPLAIN(exp) on the output
   * channel of the theory of strings.
   *
   * Determining which case to apply depends on the form of eq and whether
   * exp_n is empty. In particular, lemmas must be used whenever exp_n is
   * non-empty, conflicts are used when exp_n is empty and eq is false.
   *
   * The argument c is a string identifying the reason for inference, used for
   * debugging.
   *
   * If the flag asLemma is true, then this method will send a lemma instead
   * of an inference whenever applicable.
   */
  void sendInference(std::vector<Node>& exp,
                     std::vector<Node>& exp_n,
                     Node eq,
                     const char* c,
                     bool asLemma = false);
  /** same as above, but where exp_n is empty */
  void sendInference(std::vector<Node>& exp,
                     Node eq,
                     const char* c,
                     bool asLemma = false);
  /** Send split
   *
   * This requests that ( a = b V a != b ) is sent on the output channel as a
   * lemma. We additionally request a phase requirement for the equality a=b
   * with polarity preq.
   *
   * The argument c is a string identifying the reason for inference, used for
   * debugging.
   *
   * This method returns true if the split was non-trivial, and false
   * otherwise. A split is trivial if a=b rewrites to a constant.
   */
  bool sendSplit(Node a, Node b, const char* c, bool preq = true);
  /** Send phase requirement
   *
   * This method is called to indicate this class should send a phase
   * requirement request to the output channel for literal lit to be
   * decided with polarity pol.
   */
  void sendPhaseRequirement(Node lit, bool pol);
  /** Do pending facts
   *
   * This method asserts pending facts (d_pending) with explanations
   * (d_pendingExp) to the equality engine of the theory of strings via calls
   * to assertPendingFact in the theory of strings.
   *
   * It terminates early if a conflict is encountered, for instance, by
   * equality reasoning within the equality engine.
   *
   * Regardless of whether a conflict is encountered, the vector d_pending
   * and map d_pendingExp are cleared.
   */
  void doPendingFacts();
  /** Do pending lemmas
   *
   * This method flushes all pending lemmas (d_pending_lem) to the output
   * channel of theory of strings.
   *
   * Like doPendingFacts, this function will terminate early if a conflict
   * has already been encountered by the theory of strings. The vector
   * d_pending_lem is cleared regardless of whether a conflict is discovered.
   *
   * Notice that as a result of the above design, some lemmas may be "dropped"
   * if a conflict is discovered in between when a lemma is added to the
   * pending vector of this class (via a sendInference call). Lemmas
   * e.g. those that are required for initialization should not be sent via
   * this class, since they should never be dropped.
   */
  void doPendingLemmas();
  /**
   * Have we processed an inference during this call to check? In particular,
   * this returns true if we have a pending fact or lemma, or have encountered
   * a conflict.
   */
  bool hasProcessed() const
  {
    return hasConflict() || !d_pendingLem.empty() || !d_pending.empty();
  }
  /** Do we have a pending fact to add to the equality engine? */
  bool hasPendingFact() const { return !d_pending.empty(); }
  /** Do we have a pending lemma to send on the output channel? */
  bool hasPendingLemma() const { return !d_pendingLem.empty(); }
  /** Are we in conflict? */
  bool hasConflict() const;

 private:
  /**
   * Indicates that ant => conc should be sent on the output channel of this
   * class. This will either trigger an immediate call to the conflict
   * method of the output channel of this class of conc is false, or adds the
   * above lemma to the lemma cache d_pending_lem, which may be flushed
   * later within the current call to TheoryStrings::check.
   *
   * The argument c is a string identifying the reason for inference, used for
   * debugging.
   */
  void sendLemma(Node ant, Node conc, const char* c);
  /**
   * Indicates that conc should be added to the equality engine of this class
   * with explanation eq_exp. It must be the case that eq_exp is a (conjunction
   * of) literals that each are explainable, i.e. they already hold in the
   * equality engine of this class.
   */
  void sendInfer(Node eq_exp, Node eq, const char* c);

  /** the parent theory of strings object */
  TheoryStrings& d_parent;
  /** the equality engine
   *
   * This is a reference to the equality engine of the theory of strings.
   */
  eq::EqualityEngine& d_ee;
  /** the output channel
   *
   * This is a reference to the output channel of the theory of strings.
   */
  OutputChannel& d_out;
  /** Common constants */
  Node d_true;
  Node d_false;
  /** The list of pending literals to assert to the equality engine */
  std::vector<Node> d_pending;
  /** A map from the literals in the above vector to their explanation */
  std::map<Node, Node> d_pendingExp;
  /** A map from literals to their pending phase requirement */
  std::map<Node, bool> d_pendingReqPhase;
  /** A list of pending lemmas to be sent on the output channel. */
  std::vector<Node> d_pendingLem;
  /**
   * The keep set of this class. This set is maintained to ensure that
   * facts and their explanations are ref-counted. Since facts and their
   * explanations are SAT-context-dependent, this set is also
   * SAT-context-dependent.
   */
  NodeSet d_keep;
  /** infer substitution proxy vars
   *
   * This method attempts to (partially) convert the formula n into a
   * substitution of the form:
   *   v1 -> s1, ..., vn -> sn
   * where s1 ... sn are proxy variables and v1 ... vn are either variables
   * or constants.
   *
   * This method ensures that P ^ v1 = s1 ^ ... ^ vn = sn ^ unproc is equivalent
   * to P ^ n, where P is the conjunction of equalities corresponding to the
   * definition of all proxy variables introduced by the theory of strings.
   *
   * For example, say that v1 was introduced as a proxy variable for "ABC", and
   * v2 was introduced as a proxy variable for "AA".
   *
   * Given the input n := v1 = "ABC" ^ v2 = x ^ x = "AA", this method sets:
   * vars = { x },
   * subs = { v2 },
   * unproc = {}.
   * In particular, this says that the information content of n is essentially
   * x = v2. The first and third conjunctions can be dropped from the
   * explanation since these equalities simply correspond to definitions
   * of proxy variables.
   *
   * This method is used as a performance heuristic. It can infer when the
   * explanation of a fact depends only trivially on equalities corresponding
   * to definitions of proxy variables, which can be omitted since they are
   * assumed to hold globally.
   */
  void inferSubstitutionProxyVars(Node n,
                                  std::vector<Node>& vars,
                                  std::vector<Node>& subs,
                                  std::vector<Node>& unproc) const;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif
