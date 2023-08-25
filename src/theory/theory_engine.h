/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY_ENGINE_H
#define CVC5__THEORY_ENGINE_H

#include <memory>
#include <vector>

#include "base/check.h"
#include "context/cdhashmap.h"
#include "expr/node.h"
#include "options/theory_options.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/atom_requests.h"
#include "theory/engine_output_channel.h"
#include "theory/interrupted.h"
#include "theory/partition_generator.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/theory.h"
#include "theory/theory_engine_module.h"
#include "theory/theory_engine_statistics.h"
#include "theory/theory_preprocessor.h"
#include "theory/trust_substitutions.h"
#include "theory/uf/equality_engine.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class Env;
class ResourceManager;
class TheoryEngineProofGenerator;
class ProofChecker;

/**
 * A pair of a theory and a node. This is used to mark the flow of
 * propagations between theories.
 */
struct NodeTheoryPair {
  Node d_node;
  theory::TheoryId d_theory;
  size_t d_timestamp;
  NodeTheoryPair(TNode n, theory::TheoryId t, size_t ts = 0)
      : d_node(n), d_theory(t), d_timestamp(ts)
  {
  }
  NodeTheoryPair() : d_theory(theory::THEORY_LAST), d_timestamp() {}
  // Comparison doesn't take into account the timestamp
  bool operator == (const NodeTheoryPair& pair) const {
    return d_node == pair.d_node && d_theory == pair.d_theory;
  }
};/* struct NodeTheoryPair */

struct NodeTheoryPairHashFunction {
  std::hash<Node> hashFunction;
  // Hash doesn't take into account the timestamp
  size_t operator()(const NodeTheoryPair& pair) const {
    uint64_t hash = fnv1a::fnv1a_64(std::hash<Node>()(pair.d_node));
    return static_cast<size_t>(fnv1a::fnv1a_64(pair.d_theory, hash));
  }
};/* struct NodeTheoryPairHashFunction */


/* Forward declarations */
namespace theory {

class CombinationEngine;
class DecisionManager;
class RelevanceManager;
class Rewriter;
class SharedSolver;
class TheoryModel;

}  // namespace theory

namespace prop {
class PropEngine;
}

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * cvc5.
 */
class TheoryEngine : protected EnvObj
{
  /** Shared terms database can use the internals notify the theories */
  friend class SharedTermsDatabase;
  friend class theory::EngineOutputChannel;
  friend class theory::CombinationEngine;
  friend class theory::SharedSolver;

 public:
  /** Constructs a theory engine */
  TheoryEngine(Env& env);

  /** Destroys a theory engine */
  ~TheoryEngine();

  void interrupt();

  /** "Spend" a resource during a search or preprocessing.*/
  void spendResource(Resource r);

  /**
   * Adds a theory. Only one theory per TheoryId can be present, so if
   * there is another theory it will be deleted.
   */
  template <class TheoryClass>
  void addTheory(theory::TheoryId theoryId)
  {
    Assert(d_theoryTable[theoryId] == NULL && d_theoryOut[theoryId] == NULL);
    d_theoryOut[theoryId] =
        new theory::EngineOutputChannel(statisticsRegistry(), this, theoryId);
    d_theoryTable[theoryId] =
        new TheoryClass(d_env, *d_theoryOut[theoryId], theory::Valuation(this));
    getRewriter()->registerTheoryRewriter(
        theoryId, d_theoryTable[theoryId]->getTheoryRewriter());
  }

  /** Register theory proof rule checkers to the given proof checker */
  void initializeProofChecker(ProofChecker* pc);

  void setPropEngine(prop::PropEngine* propEngine)
  {
    d_propEngine = propEngine;
  }

  /**
   * Called when all initialization of options/logic is done, after theory
   * objects have been created.
   *
   * This initializes the quantifiers engine, the "official" equality engines
   * of each theory as required, and the model and model builder utilities.
   */
  void finishInit();

  /**
   * Get a pointer to the underlying propositional engine.
   */
  prop::PropEngine* getPropEngine() const { return d_propEngine; }

  /**
   * Get a pointer to the underlying quantifiers engine.
   */
  theory::QuantifiersEngine* getQuantifiersEngine() const
  {
    return d_quantEngine;
  }
  /**
   * Get a pointer to the underlying decision manager.
   */
  theory::DecisionManager* getDecisionManager() const
  {
    return d_decManager.get();
  }

  /**
   * Preprocess rewrite, called:
   * (1) on equalities by the preprocessor to rewrite equalities appearing in
   * the input,
   * (2) on non-equalities by the theory preprocessor.
   *
   * Calls the ppRewrite of the theory of term and adds the associated skolem
   * lemmas to lems, for details see Theory::ppRewrite.
   */
  TrustNode ppRewrite(TNode term, std::vector<theory::SkolemLemma>& lems);
  /**
   * Same as above, but applied only at preprocess time.
   */
  TrustNode ppStaticRewrite(TNode term);
  /** Notify (preprocessed) assertions. */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);

  /**
   * Return whether or not we are model unsound (in the current SAT context).
   * For details, see theory_inference_manager.
   */
  bool isModelUnsound() const { return d_modelUnsound; }
  /**
   * Return whether or not we are refutation unsound (in the current user
   * context). For details, see theory_inference_manager.
   */
  bool isRefutationUnsound() const { return d_refutationUnsound; }

  /**
   * Returns true if we need another round of checking.  If this
   * returns true, check(FULL_EFFORT) _must_ be called by the
   * propositional layer before reporting SAT.
   *
   * This is especially necessary for incomplete theories that lazily
   * output some lemmas on FULL_EFFORT check (e.g. quantifier reasoning
   * outputing quantifier instantiations).  In such a case, a lemma can
   * be asserted that is simplified away (perhaps it's already true).
   * However, we must maintain the invariant that, if a theory uses the
   * OutputChannel, it implicitly requests that another check(FULL_EFFORT)
   * be performed before exit, even if no new facts are on its fact queue,
   * as it might decide to further instantiate some lemmas, precluding
   * a SAT response.
   */
  bool needCheck() const { return d_outputChannelUsed || d_lemmasAdded; }
  /**
   * Is the literal lit (possibly) critical for satisfying the input formula in
   * the current context? This call is applicable only during collectModelInfo
   * or during LAST_CALL effort.
   */
  bool isRelevant(Node lit) const;
  /**
   * Returns true if the node has a current SAT assignment. If yes, the
   * argument "value" is set to its value.
   *
   * @return true if the literal has a current assignment, and returns the
   * value in the "value" argument; otherwise false and the "value"
   * argument is unmodified.
   */
  bool hasSatValue(TNode n, bool& value) const;
  /**
   * Same as above, without setting the value.
   */
  bool hasSatValue(TNode n) const;
  /**
   * Solve the given literal with a theory that owns it. The proof of tliteral
   * is carried in the trust node. The proof added to substitutionOut should
   * take this proof into account (when proofs are enabled).
   */
  theory::Theory::PPAssertStatus solve(
      TrustNode tliteral, theory::TrustSubstitutionMap& substitutionOut);

  /**
   * Preregister a Theory atom with the responsible theory (or
   * theories).
   */
  void preRegister(TNode preprocessed);

  /**
   * Assert the formula to the appropriate theory.
   * @param node the assertion
   */
  void assertFact(TNode node);

  /**
   * Check all (currently-active) theories for conflicts.
   * @param effort the effort level to use
   */
  void check(theory::Theory::Effort effort);

  /**
   * Calls ppStaticLearn() on all theories, accumulating their
   * combined contributions in the "learned" builder.
   */
  void ppStaticLearn(TNode in, NodeBuilder& learned);

  /**
   * Calls presolve() on all theories and returns true
   * if one of the theories discovers a conflict.
   */
  bool presolve();

  /**
   * Resets the internal state.
   */
  void postsolve();

  /**
   * Calls notifyRestart() on all active theories.
   */
  void notifyRestart();

  void getPropagatedLiterals(std::vector<TNode>& literals)
  {
    for (; d_propagatedLiteralsIndex < d_propagatedLiterals.size();
         d_propagatedLiteralsIndex = d_propagatedLiteralsIndex + 1)
    {
      Trace("getPropagatedLiterals")
          << "TheoryEngine::getPropagatedLiterals: propagating: "
          << d_propagatedLiterals[d_propagatedLiteralsIndex] << std::endl;
      literals.push_back(d_propagatedLiterals[d_propagatedLiteralsIndex]);
    }
  }

  /**
   * Returns the next decision request, or null if none exist. The next
   * decision request is a literal that this theory engine prefers the SAT
   * solver to make as its next decision. Decision requests are managed by
   * the decision manager d_decManager.
   */
  Node getNextDecisionRequest();

  bool properConflict(TNode conflict) const;

  /**
   * Returns an explanation of the node propagated to the SAT solver.
   */
  TrustNode getExplanation(TNode node);

  /**
   * Get the pointer to the model object used by this theory engine.
   */
  theory::TheoryModel* getModel();
  /**
   * Get the current model for the current set of assertions. This method
   * should only be called immediately after a satisfiable response to a
   * check-sat call, and only if produceModels is true.
   *
   * If the model is not already built, this will cause this theory engine to
   * build the model.
   *
   * If the model cannot be built, then this returns the null pointer.
   */
  theory::TheoryModel* getBuiltModel();
  /**
   * This forces the model maintained by the combination engine to be built
   * if it has not been done so already. This should be called only during a
   * last call effort check after theory combination is run.
   *
   * @return true if the model was successfully built (possibly prior to this
   * call).
   */
  bool buildModel();

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  theory::Theory* theoryOf(TNode node) const
  {
    return d_theoryTable[d_env.theoryOf(node)];
  }

  /**
   * Get the theory associated to a the given theory id.
   *
   * @returns the theory
   */
  theory::Theory* theoryOf(theory::TheoryId theoryId) const
  {
    Assert(theoryId < theory::THEORY_LAST);
    return d_theoryTable[theoryId];
  }

  bool isTheoryEnabled(theory::TheoryId theoryId) const;
  /** return the theory that should explain a propagation from TheoryId */
  theory::TheoryId theoryExpPropagation(theory::TheoryId tid) const;

  /**
   * Returns the equality status of the two terms, from the theory
   * that owns the domain type.  The types of a and b must be the same.
   */
  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Returns the value that a theory that owns the type of var currently
   * has (or null if none);
   */
  Node getCandidateModelValue(TNode var);

  /**
   * Get relevant assertions. This returns a set of assertions that are
   * currently asserted to this TheoryEngine that propositionally entail the
   * (preprocessed) input formula and all theory lemmas that have been marked
   * NEEDS_JUSTIFY. For more details on this, see relevance_manager.h.
   *
   * This method updates success to false if the set of relevant assertions
   * is not available. This may occur if we are not in SAT mode, if the
   * relevance manager is disabled (see option::relevanceFilter) or if the
   * relevance manager failed to compute relevant assertions due to an internal
   * error.
   */
  std::unordered_set<TNode> getRelevantAssertions(bool& success);

  /**
   * Get difficulty map, which populates dmap, mapping preprocessed assertions
   * to a value that estimates their difficulty for solving the current problem.
   *
   * For details, see theory/difficuly_manager.h.
   */
  void getDifficultyMap(std::map<Node, Node>& dmap, bool includeLemmas = false);

  /** Get incomplete id, valid when isModelUnsound is true. */
  theory::IncompleteId getModelUnsoundId() const;
  /** Get unsound id, valid when isRefutationUnsound is true. */
  theory::IncompleteId getRefutationUnsoundId() const;

  /**
   * Forwards an entailment check according to the given theoryOfMode.
   * See theory.h for documentation on entailmentCheck().
   */
  std::pair<bool, Node> entailmentCheck(options::TheoryOfMode mode, TNode lit);

  theory::SortInference* getSortInference() { return d_sortInfer.get(); }

  /** Prints the assertions to the debug stream */
  void printAssertions(const char* tag);

  /**
   * Check that the theory assertions are satisfied in the model.
   * This function is called from the smt engine's checkModel routine.
   */
  void checkTheoryAssertionsWithModel(bool hardFailure);

 private:
  typedef context::
      CDHashMap<NodeTheoryPair, NodeTheoryPair, NodeTheoryPairHashFunction>
          PropagationMap;

  /**
   * Called by the theories to notify of a conflict.
   *
   * @param conflict The trust node containing the conflict and its proof
   * generator (if it exists),
   * @param theoryId The theory that sent the conflict
   */
  void conflict(TrustNode conflict, theory::TheoryId theoryId);

  /** set in conflict */
  void markInConflict();

  /** Called by the theories to notify that the current branch is incomplete. */
  void setModelUnsound(theory::TheoryId theory, theory::IncompleteId id);
  /** Called by the theories to notify that we are unsound (user-context). */
  void setRefutationUnsound(theory::TheoryId theory, theory::IncompleteId id);

  /**
   * Called by the output channel to propagate literals and facts
   * @return false if immediate conflict
   */
  bool propagate(TNode literal, theory::TheoryId theory);

  /**
   * Internal method to call the propagation routines and collect the
   * propagated literals.
   */
  void propagate(theory::Theory::Effort effort);

  /**
   * Assert the formula to the given theory.
   * @param assertion the assertion to send (not necesserily normalized)
   * @param original the assertion as it was sent in from the propagating theory
   * @param toTheoryId the theory to assert to
   * @param fromTheoryId the theory that sent it
   */
  void assertToTheory(TNode assertion,
                      TNode originalAssertion,
                      theory::TheoryId toTheoryId,
                      theory::TheoryId fromTheoryId);

  /**
   * Marks a theory propagation from a theory to a theory where a
   * theory could be the THEORY_SAT_SOLVER for literals coming from
   * or being propagated to the SAT solver. If the receiving theory
   * already recieved the literal, the method returns false, otherwise
   * it returns true.
   *
   * @param assertion the normalized assertion being sent
   * @param originalAssertion the actual assertion that was sent
   * @param toTheoryId the theory that is on the receiving end
   * @param fromTheoryId the theory that sent the assertion
   * @return true if a new assertion, false if theory already got it
   */
  bool markPropagation(TNode assertion,
                       TNode originalAssertions,
                       theory::TheoryId toTheoryId,
                       theory::TheoryId fromTheoryId);

  /**
   * Computes the explanation by traversing the propagation graph and
   * asking relevant theories to explain the propagations. Initially
   * the explanation vector should contain only the element (node, theory)
   * where the node is the one to be explained, and the theory is the
   * theory that sent the literal.
   */
  TrustNode getExplanation(std::vector<NodeTheoryPair>& explanationVector);

  /** Are proofs enabled? */
  bool isProofEnabled() const;

  /**
   * Get a pointer to the rewriter owned by the associated Env.
   */
  theory::Rewriter* getRewriter();

  /**
   * Adds a new lemma, returning its status.
   * @param node the lemma
   * @param p the properties of the lemma.
   * @param atomsTo the theory that atoms of the lemma should be sent to
   * @param from the theory that sent the lemma
   */
  void lemma(TrustNode node,
             theory::LemmaProperty p,
             theory::TheoryId from = theory::THEORY_LAST);

  /** Ensure atoms from the given node are sent to the given theory */
  void ensureLemmaAtoms(TNode n, theory::TheoryId atomsTo);
  /** Ensure that the given atoms are sent to the given theory */
  void ensureLemmaAtoms(const std::vector<TNode>& atoms,
                        theory::TheoryId atomsTo);

  /** Associated PropEngine engine */
  prop::PropEngine* d_propEngine;

  /**
   * A table of from theory IDs to theory pointers. Never use this table
   * directly, use theoryOf() instead.
   */
  theory::Theory* d_theoryTable[theory::THEORY_LAST];

  //--------------------------------- proofs
  /** The lazy proof object
   *
   * This stores instructions for how to construct proofs for all theory lemmas.
   */
  std::shared_ptr<LazyCDProof> d_lazyProof;
  /** The proof generator */
  std::shared_ptr<TheoryEngineProofGenerator> d_tepg;
  //--------------------------------- end proofs
  /** The combination manager we are using */
  std::unique_ptr<theory::CombinationEngine> d_tc;
  /** The shared solver of the above combination engine. */
  theory::SharedSolver* d_sharedSolver;
  /** The quantifiers engine, which is owned by the quantifiers theory */
  theory::QuantifiersEngine* d_quantEngine;
  /**
   * The decision manager
   */
  std::unique_ptr<theory::DecisionManager> d_decManager;
  /** The relevance manager */
  std::unique_ptr<theory::RelevanceManager> d_relManager;

  /**
   * Output channels for individual theories.
   */
  theory::EngineOutputChannel* d_theoryOut[theory::THEORY_LAST];

  /**
   * Are we in conflict.
   */
  context::CDO<bool> d_inConflict;

  /**
   * True if a theory has notified us of model unsoundness (at this SAT
   * context level or below). For details, see theory_inference_manager.
   */
  context::CDO<bool> d_modelUnsound;
  /** The theory and identifier that (most recently) set model unsound */
  context::CDO<theory::TheoryId> d_modelUnsoundTheory;
  context::CDO<theory::IncompleteId> d_modelUnsoundId;
  /**
   * True if a theory has notified us of refutation unsoundness (at this user
   * context level or below).
   */
  context::CDO<bool> d_refutationUnsound;
  /** The theory and identifier that (most recently) set incomplete */
  context::CDO<theory::TheoryId> d_refutationUnsoundTheory;
  context::CDO<theory::IncompleteId> d_refutationUnsoundId;

  /**
   * Mapping of propagations from recievers to senders.
   */
  PropagationMap d_propagationMap;

  /**
   * Timestamp of propagations
   */
  context::CDO<size_t> d_propagationMapTimestamp;

  /**
   * Literals that are propagated by the theory. Note that these are TNodes.
   * The theory can only propagate nodes that have an assigned literal in the
   * SAT solver and are hence referenced in the SAT solver.
   */
  context::CDList<TNode> d_propagatedLiterals;

  /**
   * The index of the next literal to be propagated by a theory.
   */
  context::CDO<unsigned> d_propagatedLiteralsIndex;

  /**
   * A variable to mark if we added any lemmas.
   */
  bool d_lemmasAdded;

  /**
   * A variable to mark if the OutputChannel was "used" by any theory
   * since the start of the last check.  If it has been, we require
   * a FULL_EFFORT check before exiting and reporting SAT.
   *
   * See the documentation for the needCheck() function, below.
   */
  bool d_outputChannelUsed;

  /** Atom requests from lemmas */
  AtomRequests d_atomRequests;

  /** sort inference module */
  std::unique_ptr<theory::SortInference> d_sortInfer;

  /** Statistics */
  theory::TheoryEngineStatistics d_stats;

  Node d_true;
  Node d_false;

  /** Whether we were just interrupted (or not) */
  bool d_interrupted;

  /**
   * Queue of nodes for pre-registration.
   */
  std::queue<TNode> d_preregisterQueue;

  /**
   * Boolean flag denoting we are in pre-registration.
   */
  bool d_inPreregister;

  /**
   * Did the theories get any new facts since the last time we called
   * check()
   */
  context::CDO<bool> d_factsAsserted;

  /**
   * The splitter produces partitions when the compute-partitions option is
   * used.
   */
  std::unique_ptr<theory::PartitionGenerator> d_partitionGen;
  /** The list of modules */
  std::vector<theory::TheoryEngineModule*> d_modules;

}; /* class TheoryEngine */

}  // namespace cvc5::internal

#endif /* CVC5__THEORY_ENGINE_H */
