/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The PropEngine (propositional engine).
 *
 * Main interface point between cvc5's SMT infrastructure and the SAT solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP_ENGINE_H
#define CVC5__PROP_ENGINE_H

#include <cvc5/cvc5_types.h>

#include "context/cdlist.h"
#include "expr/node.h"
#include "proof/proof.h"
#include "proof/trust_node.h"
#include "prop/learned_db.h"
#include "prop/skolem_def_manager.h"
#include "smt/env_obj.h"
#include "theory/output_channel.h"
#include "theory/skolem_lemma.h"
#include "util/result.h"

namespace cvc5::internal {

class ResourceManager;
class ProofNodeManager;
class TheoryEngine;

namespace decision {
class DecisionEngine;
}

namespace prop {

class CnfStream;
class CDCLTSatSolver;
class ProofCnfStream;
class PropPfManager;
class TheoryProxy;

/**
 * PropEngine is the abstraction of a Sat Solver, providing methods for
 * solving the SAT problem and conversion to CNF (via the CnfStream).
 */
class PropEngine : protected EnvObj
{
 public:
  /**
   * Create a PropEngine with a particular decision and theory engine.
   */
  PropEngine(Env& env, TheoryEngine* te);

  /**
   * Destructor.
   */
  ~PropEngine();

  /**
   * Finish initialize. Call this after construction just before we are
   * ready to use this class. Should be called after TheoryEngine::finishInit.
   * This method converts and asserts true and false into the CNF stream.
   */
  void finishInit();

  /**
   * Preprocess the given node. Return the REWRITE trust node corresponding to
   * rewriting node. New lemmas and skolems are added to ppLemmas and
   * ppSkolems respectively.
   *
   * @param node The assertion to preprocess,
   * @param ppLemmas The lemmas to add to the set of assertions, which tracks
   * their corresponding skolems,
   * @return The (REWRITE) trust node corresponding to rewritten node via
   * preprocessing.
   */
  TrustNode preprocess(TNode node, std::vector<theory::SkolemLemma>& ppLemmas);
  /**
   * Remove term ITEs (and more generally, term formulas) from the given node.
   * Return the REWRITE trust node corresponding to rewriting node. New lemmas
   * and skolems are added to ppLemmas and ppSkolems respectively. This can
   * be seen a subset of the above preprocess method, which also does theory
   * preprocessing and rewriting.
   *
   * @param node The assertion to preprocess,
   * @param ppLemmas The lemmas to add to the set of assertions, which tracks
   * their corresponding skolems.
   * @return The (REWRITE) trust node corresponding to rewritten node via
   * preprocessing.
   */
  TrustNode removeItes(TNode node, std::vector<theory::SkolemLemma>& ppLemmas);

  /**
   * Notify that lhs was substituted by rhs during preprocessing. This impacts
   * the tracked learned literals and output traces.
   * @param lhs The left-hand side of the substitution
   * @param rhs The right-hand side of the substitution
   */
  void notifyTopLevelSubstitution(const Node& lhs, const Node& rhs) const;
  /**
   * Converts the given formulas to CNF and assert the CNF to the SAT solver.
   * These formulas are asserted permanently for the current context.
   * Information about which assertions correspond to skolem definitions is
   * contained in skolemMap.
   *
   * @param assertions the formulas to assert
   * @param skolemMap a map which says which skolem (if any) each assertion
   * corresponds to. For example, if (ite C (= k a) (= k b)) is the i^th
   * assertion, then skolemMap may contain the entry { i -> k }.
   */
  void assertInputFormulas(const std::vector<Node>& assertions,
                           std::unordered_map<size_t, Node>& skolemMap);

  /**
   * Converts the given formula to CNF and assert the CNF to the SAT solver.
   * The formula can be removed by the SAT solver after backtracking lower
   * than the (SAT and SMT) level at which it was asserted.
   *
   * @param trn the trust node storing the formula to assert
   * @param p the properties of the lemma
   */
  void assertLemma(TrustNode tlemma, theory::LemmaProperty p);

  /**
   * If ever n is decided upon, it must be in the given phase.  This
   * occurs *globally*, i.e., even if the literal is untranslated by
   * user pop and retranslated, it keeps this phase.  The associated
   * variable will _always_ be phase-locked.
   *
   * @param n the node in question; must have an associated SAT literal
   * @param phase the phase to use
   */
  void requirePhase(TNode n, bool phase);

  /**
   * Return whether the given literal is a SAT decision.  Either phase
   * is permitted; that is, if "lit" is a SAT decision, this function
   * returns true for both lit and the negation of lit.
   */
  bool isDecision(Node lit) const;

  /**
   * Get the current list of decisions made by the SAT solver at the moment in
   * time that getPropDecisions() is called.
   *
   * @return List of decisions made by the SAT solver.
   */
  std::vector<Node> getPropDecisions() const;

  /**
   * Get the order heap from the SAT solver.
   * order_heap is a priority queue of variables ordered with
   * respect to the variable activity. The order heap is made available here
   * in order to make partitions based on the literals contained in the heap.
   *
   * @return List of Nodes from the SAT variables order heap.
   */
  std::vector<Node> getPropOrderHeap() const;

  /**
   * Return whether lit has a fixed SAT assignment (i.e., implied by input
   * assertions).
   */
  bool isFixed(TNode lit) const;

  /**
   * Checks the current context for satisfiability.
   *
   */
  Result checkSat();

  /**
   * Get the value of a boolean variable.
   *
   * @return mkConst<true>, mkConst<false>, or Node::null() if
   * unassigned.
   */
  Node getValue(TNode node) const;

  /**
   * Return true if node has an associated SAT literal.
   */
  bool isSatLiteral(TNode node) const;

  /**
   * Check if the node has a value and return it if yes.
   */
  bool hasValue(TNode node, bool& value) const;

  /**
   * Returns the Boolean variables known to the SAT solver.
   */
  void getBooleanVariables(std::vector<TNode>& outputVariables) const;

  /**
   * Ensure that the given node will have a designated SAT literal
   * that is definitionally equal to it. Note that theory preprocessing is
   * applied to n. The node returned by this method can be subsequently queried
   * via getSatValue().
   */
  Node ensureLiteral(TNode n);
  /**
   * This returns the theory-preprocessed form of term n. This rewrites and
   * preprocesses n, which notice may involve adding clauses to the SAT solver
   * if preprocessing n involves introducing new skolems.
   */
  Node getPreprocessedTerm(TNode n);
  /**
   * Same as above, but also compute the skolems in n and in the lemmas
   * corresponding to their definition.
   *
   * Note this will include skolems that occur in the definition lemma
   * for all skolems in sks. This is run until a fixed point is reached.
   * For example, if k1 has definition (ite A (= k1 k2) (= k1 x)) where k2 is
   * another skolem introduced by term formula removal, then calling this
   * method on (P k1) will include both k1 and k2 in sks, and their definitions
   * in skAsserts.
   *
   * Notice that this method is not frequently used. It is used for algorithms
   * that explicitly care about knowing which skolems occur in the preprocessed
   * form of a term, recursively.
   */
  Node getPreprocessedTerm(TNode n,
                           std::vector<Node>& skAsserts,
                           std::vector<Node>& sks);

  /**
   * Push the context level.
   */
  void push();

  /**
   * Pop the context level.
   */
  void pop();

  /*
   * Reset the decisions in the DPLL(T) SAT solver at the current assertion
   * level.
   */
  void resetTrail();

  /**
   * Get the assertion level of the SAT solver.
   */
  uint32_t getAssertionLevel() const;

  /**
   * Return true if we are currently searching (either in this or
   * another thread).
   */
  bool isRunning() const;

  /**
   * Interrupt a running solver (cause a timeout).
   *
   * Can potentially throw a ModalException.
   */
  void interrupt();

  /**
   * Informs the ResourceManager that a resource has been spent.  If out of
   * resources, the solver is interrupted using a callback.
   */
  void spendResource(Resource r);

  /**
   * For debugging.  Return true if "expl" is a well-formed
   * explanation for "node," meaning:
   *
   * 1. expl is either a SAT literal or an AND of SAT literals
   *    currently assigned true;
   * 2. node is assigned true;
   * 3. node does not appear in expl; and
   * 4. node was assigned after all of the literals in expl
   */
  bool properExplanation(TNode node, TNode expl) const;

  /** Get the associated CNF stream. */
  CnfStream* getCnfStream();
  /** Retrieve this modules proof CNF stream. */
  ProofCnfStream* getProofCnfStream();

  /** Checks that the proof is closed w.r.t. asserted formulas to this engine as
   * well as to the given assertions. */
  void checkProof(const context::CDList<Node>& assertions);

  /**
   * Return the prop engine proof. This should be called only when proofs are
   * enabled. Returns a proof of false whose free assumptions are the
   * preprocessed assertions.
   *
   * @param connectCnf If this flag is false, then all clausified preprocessed
   * assertion and theory lemmas are free assumptions in the returned proof
   * instead of being connected to their proofs.
   */
  std::shared_ptr<ProofNode> getProof(bool connectCnf = true);

  /** Return the vector of proofs for the respective proof component requested.
   *
   * The components may be of theory lemma proofs (closed proofs of valid theory
   * clauses) or of preprocessed assertion proofs (them the preprocessed
   * assertion assumptions to the added clauses to the SAT solver).
   */
  std::vector<std::shared_ptr<ProofNode>> getProofLeaves(
      modes::ProofComponent pc);

  /** Is proof enabled? */
  bool isProofEnabled() const;

  /**
   * Retrieve unsat core of preprocessing assertions.
   *
   * For assumption-based unsat cores, this is retrived from the SAT solver.
   * For proof-based unsat cores, this is computed via the free assumptions of
   * the proof.
   */
  void getUnsatCore(std::vector<Node>& core);

  /** Get the zero-level assertions of the given type */
  std::vector<Node> getLearnedZeroLevelLiterals(
      modes::LearnedLitType ltype) const;

  /** Get the zero-level assertions that should be used on deep restart */
  std::vector<Node> getLearnedZeroLevelLiteralsForRestart() const;

  /** Get the literal type through the ZLL utilities */
  modes::LearnedLitType getLiteralType(const Node& lit) const;

 private:
  /** Dump out the satisfying assignment (after SAT result) */
  void printSatisfyingAssignment();
  /** Print reason for answering unknown on output when applicable */
  void outputIncompleteReason(
      UnknownExplanation uexp,
      theory::IncompleteId iid = theory::IncompleteId::UNKNOWN);

  /**
   * Converts the given formula to CNF and asserts the CNF to the SAT solver.
   * The formula can be removed by the SAT solver after backtracking lower
   * than the (SAT and SMT) level at which it was asserted.
   *
   * @param trn the trust node storing the formula to assert
   * @param removable whether this lemma can be quietly removed based
   * on an activity heuristic
   */
  void assertTrustedLemmaInternal(TrustNode trn, bool removable);
  /**
   * Assert node as a formula to the CNF stream
   * @param node The formula to assert
   * @param negated Whether to assert the negation of node
   * @param removable Whether the formula is removable
   * @param input Whether the formula came from the input
   * @param pg Pointer to a proof generator that can provide a proof of node
   * (or its negation if negated is true).
   */
  void assertInternal(TNode node,
                      bool negated,
                      bool removable,
                      bool input,
                      ProofGenerator* pg = nullptr);
  /**
   * Assert lemmas internal, where trn is a trust node corresponding to a
   * formula to assert to the CNF stream, ppLemmas are the skolem definitions
   * obtained from preprocessing it, and removable is whether the lemma is
   * removable.
   */
  void assertLemmasInternal(TrustNode trn,
                            const std::vector<theory::SkolemLemma>& ppLemmas,
                            bool removable);

  /**
   * Indicates that the SAT solver is currently solving something and we should
   * not mess with it's internal state.
   */
  bool d_inCheckSat;

  /** The theory engine we will be using */
  TheoryEngine* d_theoryEngine;

  /** The skolem definition manager */
  std::unique_ptr<SkolemDefManager> d_skdm;

  /** SAT solver's proxy back to theories; kept around for dtor cleanup */
  TheoryProxy* d_theoryProxy;

  /** The SAT solver proxy */
  CDCLTSatSolver* d_satSolver;

  /** List of all of the assertions that need to be made */
  std::vector<Node> d_assertionList;

  /** The CNF converter in use */
  CnfStream* d_cnfStream;
  /** Proof-producing CNF converter */
  std::unique_ptr<ProofCnfStream> d_pfCnfStream;
  /** A default proof generator for theory lemmas */
  CDProof d_theoryLemmaPg;

  /** The proof manager for prop engine */
  std::unique_ptr<PropPfManager> d_ppm;

  /** Whether we were just interrupted (or not) */
  bool d_interrupted;

  /**
   * Stores assumptions added via assertInternal() if assumption-based unsat
   * cores are enabled.
   */
  context::CDList<Node> d_assumptions;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP_ENGINE_H */
