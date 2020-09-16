/*********************                                                        */
/*! \file term_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term registry for the theory of strings.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__TERM_REGISTRY_H
#define CVC4__THEORY__STRINGS__TERM_REGISTRY_H

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/proof_node_manager.h"
#include "theory/eager_proof_generator.h"
#include "theory/output_channel.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/solver_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * This class manages all the (pre)registration tasks for terms. These tasks
 * include:
 * (1) Sending out preregistration lemmas for terms,
 * (2) Add terms to the equality engine,
 * (3) Maintaining a list of terms d_functionsTerms (for theory combination),
 * (4) Maintaining a list of input variables d_inputVars (for fmf).
 * (5) Maintaining a skolem cache. Notice that this skolem cache is the
 * official skolem cache that should be used by all modules in TheoryStrings.
 */
class TermRegistry
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashSet<TypeNode, TypeNodeHashFunction> TypeNodeSet;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;

 public:
  TermRegistry(SolverState& s,
               OutputChannel& out,
               SequencesStatistics& statistics,
               ProofNodeManager* pnm);
  ~TermRegistry();
  /** The eager reduce routine
   *
   * Constructs a lemma for t that is incomplete, but communicates pertinent
   * information about t. This is analogous to StringsPreprocess::reduce.
   *
   * In practice, we send this lemma eagerly, as soon as t is registered.
   *
   * @param t The node to reduce,
   * @param sc The Skolem cache to use for new variables,
   * @return The eager reduction for t.
   */
  static Node eagerReduce(Node t, SkolemCache* sc);
  /**
   * Returns a lemma indicating that the length of a term t whose type is
   * string-like has positive length. The exact form of this lemma depends
   * on what works best in practice, currently:
   *   (or (and (= (str.len t) 0) (= t "")) (> (str.len t) 0))
   *
   * @param t The node to reduce,
   * @return The positive length lemma for t.
   */
  static Node lengthPositive(Node t);
  /**
   * Preregister term, called when TheoryStrings::preRegisterTerm(n) is called.
   * This does the following:
   * - Checks for illegal terms and throws a LogicException if any term is
   * not handled.
   * - Adds the appropriate terms and triggers to the equality engine.
   * - Updates information about which terms exist, including
   * d_functionsTerms and d_hasStrCode. If we are using strings finite model
   * finding (options::stringsFmf), we determine if the term n should be
   * added to d_inputVars, the set of terms of type string whose length we are
   * minimizing with its decision strategy.
   * - Setting phase requirements on n if it is a formula and we prefer
   * decisions with a particular polarity (e.g. positive regular expression
   * memberships).
   */
  void preRegisterTerm(TNode n);
  /** Register term
   *
   * This performs SAT-context-independent registration for a term n, which
   * may cause lemmas to be sent on the output channel that involve
   * "initial refinement lemmas" for n. This includes introducing proxy
   * variables for string terms and asserting that str.code terms are within
   * proper bounds.
   *
   * Effort is one of the following (TODO make enum #1881):
   * 0 : upon preregistration or internal assertion
   * 1 : upon occurrence in length term
   * 2 : before normal form computation
   * 3 : called on normal form terms
   *
   * Based on the strategy, we may choose to add these initial refinement
   * lemmas at one of the following efforts, where if it is not the given
   * effort, the call to this method does nothing.
   */
  void registerTerm(Node n, int effort);
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
   * If the status is LENGTH_GEQ_ONE, we send a lemma n != "" ^ len( n ) > 0.
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
  //---------------------------- queries
  /** Get the skolem cache of this object */
  SkolemCache* getSkolemCache();
  /** Get all function terms that have been preregistered to this object */
  const context::CDList<TNode>& getFunctionTerms() const;
  /**
   * Get the "input variables", corresponding to the set of leaf nodes of
   * string-like type that have been preregistered as terms to this object.
   */
  const context::CDHashSet<Node, NodeHashFunction>& getInputVars() const;
  /** Returns true if any str.code terms have been preregistered */
  bool hasStringCode() const;
  //---------------------------- end queries
  //---------------------------- proxy variables
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

  /**
   * Get the proxy variable for a term. If the proxy variable does not exist,
   * this method registers the term and then returns its proxy variable.
   *
   * @param n The term
   * @return Proxy variable for `n`
   */
  Node ensureProxyVariableFor(Node n);

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
  //---------------------------- end proxy variables
 private:
  /** Common constants */
  Node d_zero;
  Node d_one;
  Node d_negOne;
  /** the cardinality of the alphabet */
  uint32_t d_cardSize;
  /** Reference to the solver state of the theory of strings. */
  SolverState& d_state;
  /** Reference to the output channel of the theory of strings. */
  OutputChannel& d_out;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /** have we asserted any str.code terms? */
  bool d_hasStrCode;
  /** The cache of all skolems, which is owned by this class. */
  SkolemCache d_skCache;
  /** All function terms that the theory has seen in the current SAT context */
  context::CDList<TNode> d_functionsTerms;
  /**
   * The set of terms of type string that are abstracted as leaf nodes.
   */
  NodeSet d_inputVars;
  /** The user-context dependent cache of terms that have been preregistered */
  NodeSet d_preregisteredTerms;
  /** The user-context dependent cache of terms that have been registered */
  NodeSet d_registeredTerms;
  /** The types that we have preregistered */
  TypeNodeSet d_registeredTypes;
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
  /** Proof generator, manages proofs for lemmas generated by this class */
  std::unique_ptr<EagerProofGenerator> d_epg;
  /** Register type
   *
   * Ensures the theory solver is setup to handle string-like type tn. In
   * particular, this includes:
   * - Calling preRegisterTerm on the empty word for tn
   */
  void registerType(TypeNode tn);
  /** register term
   *
   * This method is called on non-constant string terms n. It returns a lemma
   * that should be sent on the output channel of theory of strings upon
   * registration of this term, or null if no lemma is necessary.
   *
   * If n is an atomic term, the method registerTermAtomic is called for n
   * and s = LENGTH_SPLIT and no lemma is returned.
   */
  TrustNode getRegisterTermLemma(Node n);
  /**
   * Get the lemma required for registering the length information for
   * atomic term n given length status s. For details, see registerTermAtomic.
   *
   * Additionally, this method may map literals to a required polarity in the
   * argument reqPhase, which should be processed by a call to requiredPhase by
   * the caller of this method.
   */
  TrustNode getRegisterTermAtomicLemma(Node n,
                                       LengthStatus s,
                                       std::map<Node, bool>& reqPhase);
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__TERM_REGISTRY_H */
