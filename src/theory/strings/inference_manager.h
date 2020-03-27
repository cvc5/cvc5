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
#include "theory/strings/infer_info.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"
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
 * theory of strings, e.g. sendPhaseRequirement, setIncomplete, and
 * with the extended theory object e.g. markCongruent.
 */
class InferenceManager
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;

 public:
  InferenceManager(TheoryStrings& p,
                   context::Context* c,
                   context::UserContext* u,
                   SolverState& s,
                   SkolemCache& skc,
                   OutputChannel& out,
                   SequencesStatistics& statistics);
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
  void sendInference(const std::vector<Node>& exp,
                     const std::vector<Node>& exp_n,
                     Node eq,
                     const char* c,
                     bool asLemma = false);
  /** same as above, but where exp_n is empty */
  void sendInference(const std::vector<Node>& exp,
                     Node eq,
                     const char* c,
                     bool asLemma = false);

  /**
   * The same as `sendInference()` above but with an `Inference` instead of a
   * string. This variant updates the statistics about the number of inferences
   * made of each type.
   */
  void sendInference(const std::vector<Node>& exp,
                     const std::vector<Node>& exp_n,
                     Node eq,
                     Inference infer,
                     bool asLemma = false);

  /**
   * The same as `sendInference()` above but with an `Inference` instead of a
   * string. This variant updates the statistics about the number of inferences
   * made of each type.
   */
  void sendInference(const std::vector<Node>& exp,
                     Node eq,
                     Inference infer,
                     bool asLemma = false);

  /** Send inference
   *
   * Makes the appropriate call to send inference based on the infer info
   * data structure (see sendInference documentation above).
   */
  void sendInference(const InferInfo& i);
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

  //---------------------------- proxy variables and length elaboration
  /** Get symbolic definition
   *
   * This method returns the "symbolic definition" of n, call it n', and
   * populates the vector exp with an explanation such that exp => n = n'.
   *
   * The symbolic definition of n is the term where (maximal) subterms of n
   * are replaced by their proxy variables. For example, if we introduced
   * proxy variable v for x ++ y, then given input x ++ y = w, this method
   * returns v = w and adds v = x ++ y to exp.
   */
  Node getSymbolicDefinition(Node n, std::vector<Node>& exp) const;
  /** Get proxy variable
   *
   * If this method returns the proxy variable for (string) term n if one
   * exists, otherwise it returns null.
   */
  Node getProxyVariableFor(Node n) const;
  /** register term
   *
   * This method is called on non-constant string terms n. It returns a lemma
   * that should be sent on the output channel of theory of strings upon
   * registration of this term, or null if no lemma is necessary.
   *
   * If n is an atomic term, the method registerTermAtomic is called for n
   * and s = LENGTH_SPLIT and no lemma is returned.
   */
  Node registerTerm(Node n);
  /** register length
   *
   * This method is called on non-constant string terms n that are "atomic"
   * with respect to length. That is, the rewritten form of len(n) is itself.
   *
   * It sends a lemma on the output channel that ensures that the length n
   * satisfies its assigned status (given by argument s).
   *
   * If the status is LENGTH_ONE, we send the lemma len( n ) = 1.
   *
   * If the status is LENGTH_GEQ, we send a lemma n != "" ^ len( n ) > 0.
   *
   * If the status is LENGTH_SPLIT, we send a send a lemma of the form:
   *   ( n = "" ^ len( n ) = 0 ) OR len( n ) > 0
   * This method also ensures that, when applicable, the left branch is taken
   * first via calls to requirePhase.
   *
   * If the status is LENGTH_IGNORE, then no lemma is sent. This status is used
   * e.g. when the length of n is already implied by other constraints.
   *
   * In contrast to the above functions, it makes immediate calls to the output
   * channel instead of adding them to pending lists.
   */
  void registerTermAtomic(Node n, LengthStatus s);
  //---------------------------- end proxy variables and length elaboration

  //----------------------------constructing antecedants
  /**
   * Adds equality a = b to the vector exp if a and b are distinct terms. It
   * must be the case that areEqual( a, b ) holds in this context.
   */
  void addToExplanation(Node a, Node b, std::vector<Node>& exp) const;
  /** Adds lit to the vector exp if it is non-null */
  void addToExplanation(Node lit, std::vector<Node>& exp) const;
  //----------------------------end constructing antecedants
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
  bool hasProcessed() const;
  /** Do we have a pending fact to add to the equality engine? */
  bool hasPendingFact() const { return !d_pending.empty(); }
  /** Do we have a pending lemma to send on the output channel? */
  bool hasPendingLemma() const { return !d_pendingLem.empty(); }

  /** make explanation
   *
   * This returns a node corresponding to the explanation of formulas in a,
   * interpreted conjunctively. The returned node is a conjunction of literals
   * that have been asserted to the equality engine.
   */
  Node mkExplain(const std::vector<Node>& a) const;
  /** Same as above, but the new literals an are append to the result */
  Node mkExplain(const std::vector<Node>& a, const std::vector<Node>& an) const;
  /**
   * Explain literal l, add conjuncts to assumptions vector instead of making
   * the node corresponding to their conjunction.
   */
  void explain(TNode literal, std::vector<TNode>& assumptions) const;
  /**
   * Set that we are incomplete for the current set of assertions (in other
   * words, we must answer "unknown" instead of "sat"); this calls the output
   * channel's setIncomplete method.
   */
  void setIncomplete();
  /**
   * Mark that terms a and b are congruent in the current context.
   * This makes a call to markCongruent in the extended theory object of
   * the parent theory if the kind of a (and b) is owned by the extended
   * theory.
   */
  void markCongruent(Node a, Node b);

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
  /**
   * Get the lemma required for registering the length information for
   * atomic term n given length status s. For details, see registerTermAtomic.
   *
   * Additionally, this method may map literals to a required polarity in the
   * argument reqPhase, which should be processed by a call to requiredPhase by
   * the caller of this method.
   */
  Node getRegisterTermAtomicLemma(Node n,
                                  LengthStatus s,
                                  std::map<Node, bool>& reqPhase);

  /** the parent theory of strings object */
  TheoryStrings& d_parent;
  /**
   * This is a reference to the solver state of the theory of strings.
   */
  SolverState& d_state;
  /** cache of all skolems */
  SkolemCache& d_skCache;
  /** the output channel
   *
   * This is a reference to the output channel of the theory of strings.
   */
  OutputChannel& d_out;

  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;

  /** Common constants */
  Node d_emptyString;
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
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
  /**
   * Map string terms to their "proxy variables". Proxy variables are used are
   * intermediate variables so that length information can be communicated for
   * constants. For example, to communicate that "ABC" has length 3, we
   * introduce a proxy variable v_{"ABC"} for "ABC", and assert:
   *   v_{"ABC"} = "ABC" ^ len( v_{"ABC"} ) = 3
   * Notice this is required since we cannot directly write len( "ABC" ) = 3,
   * which rewrites to 3 = 3.
   * In the above example, we store "ABC" -> v_{"ABC"} in this map.
   */
  NodeNodeMap d_proxyVar;
  /**
   * Map from proxy variables to their normalized length. In the above example,
   * we store "ABC" -> 3.
   */
  NodeNodeMap d_proxyVarToLength;
  /** List of terms that we have register length for */
  NodeSet d_lengthLemmaTermsCache;

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
