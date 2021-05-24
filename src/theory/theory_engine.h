/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "theory/atom_requests.h"
#include "theory/engine_output_channel.h"
#include "theory/interrupted.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/theory.h"
#include "theory/theory_preprocessor.h"
#include "theory/trust_substitutions.h"
#include "theory/uf/equality_engine.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/statistics_stats.h"
#include "util/unsafe_interrupt_exception.h"

namespace cvc5 {

class Env;
class ResourceManager;
class OutputManager;
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
class TheoryModel;
class CombinationEngine;
class SharedSolver;
class DecisionManager;
class RelevanceManager;

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
class TheoryEngine {

  /** Shared terms database can use the internals notify the theories */
  friend class SharedTermsDatabase;
  friend class theory::EngineOutputChannel;
  friend class theory::CombinationEngine;
  friend class theory::SharedSolver;

  /** Associated PropEngine engine */
  prop::PropEngine* d_propEngine;

  /**
   * Reference to the environment.
   */
  Env& d_env;

  /**
   * A table of from theory IDs to theory pointers. Never use this table
   * directly, use theoryOf() instead.
   */
  theory::Theory* d_theoryTable[theory::THEORY_LAST];

  /**
   * A collection of theories that are "active" for the current run.
   * This set is provided by the user (as a logic string, say, in SMT-LIBv2
   * format input), or else by default it's all-inclusive.  This is important
   * because we can optimize for single-theory runs (no sharing), can reduce
   * the cost of walking the DAG on registration, etc.
   */
  const LogicInfo& d_logicInfo;

  /** The separation logic location and data types */
  TypeNode d_sepLocType;
  TypeNode d_sepDataType;

  /** Reference to the output manager of the smt engine */
  OutputManager& d_outMgr;

  //--------------------------------- new proofs
  /** Proof node manager used by this theory engine, if proofs are enabled */
  ProofNodeManager* d_pnm;
  /** The lazy proof object
   *
   * This stores instructions for how to construct proofs for all theory lemmas.
   */
  std::shared_ptr<LazyCDProof> d_lazyProof;
  /** The proof generator */
  std::shared_ptr<TheoryEngineProofGenerator> d_tepg;
  //--------------------------------- end new proofs
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
   * An empty set of relevant assertions, which is returned as a dummy value for
   * getRelevantAssertions when relevance is disabled.
   */
  std::unordered_set<TNode> d_emptyRelevantSet;

  /** are we in eager model building mode? (see setEagerModelBuilding). */
  bool d_eager_model_building;

  /**
   * Output channels for individual theories.
   */
  theory::EngineOutputChannel* d_theoryOut[theory::THEORY_LAST];

  /**
   * Are we in conflict.
   */
  context::CDO<bool> d_inConflict;

  /**
   * Are we in "SAT mode"? In this state, the user can query for the model.
   * This corresponds to the state in Figure 4.1, page 52 of the SMT-LIB
   * standard, version 2.6.
   */
  bool d_inSatMode;

  /**
   * Called by the theories to notify of a conflict.
   *
   * @param conflict The trust node containing the conflict and its proof
   * generator (if it exists),
   * @param theoryId The theory that sent the conflict
   */
  void conflict(theory::TrustNode conflict, theory::TheoryId theoryId);

  /**
   * Debugging flag to ensure that shutdown() is called before the
   * destructor.
   */
  bool d_hasShutDown;

  /**
   * True if a theory has notified us of incompleteness (at this
   * context level or below).
   */
  context::CDO<bool> d_incomplete;
  /** The theory and identifier that (most recently) set incomplete */
  context::CDO<theory::TheoryId> d_incompleteTheory;
  context::CDO<theory::IncompleteId> d_incompleteId;

  /**
   * Called by the theories to notify that the current branch is incomplete.
   */
  void setIncomplete(theory::TheoryId theory, theory::IncompleteId id);

  /**
   * Mapping of propagations from recievers to senders.
   */
  typedef context::CDHashMap<NodeTheoryPair, NodeTheoryPair, NodeTheoryPairHashFunction> PropagationMap;
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

  /**
   * Adds a new lemma, returning its status.
   * @param node the lemma
   * @param p the properties of the lemma.
   * @param atomsTo the theory that atoms of the lemma should be sent to
   * @param from the theory that sent the lemma
   */
  void lemma(theory::TrustNode node,
             theory::LemmaProperty p,
             theory::TheoryId atomsTo = theory::THEORY_LAST,
             theory::TheoryId from = theory::THEORY_LAST);

  /** Enusre that the given atoms are send to the given theory */
  void ensureLemmaAtoms(const std::vector<TNode>& atoms, theory::TheoryId theory);

  /** sort inference module */
  std::unique_ptr<theory::SortInference> d_sortInfer;

  /** Time spent in theory combination */
  TimerStat d_combineTheoriesTime;

  Node d_true;
  Node d_false;

  /** Whether we were just interrupted (or not) */
  bool d_interrupted;

 public:
  /** Constructs a theory engine */
  TheoryEngine(Env& env, OutputManager& outMgr, ProofNodeManager* pnm);

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
  inline void addTheory(theory::TheoryId theoryId)
  {
    Assert(d_theoryTable[theoryId] == NULL && d_theoryOut[theoryId] == NULL);
    d_theoryOut[theoryId] = new theory::EngineOutputChannel(this, theoryId);
    d_theoryTable[theoryId] = new TheoryClass(getSatContext(),
                                              getUserContext(),
                                              *d_theoryOut[theoryId],
                                              theory::Valuation(this),
                                              d_logicInfo,
                                              d_pnm);
    theory::Rewriter::registerTheoryRewriter(
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
  inline prop::PropEngine* getPropEngine() const {
    return d_propEngine;
  }

  /** Get the proof node manager */
  ProofNodeManager* getProofNodeManager() const;

  /**
   * Get a pointer to the underlying sat context.
   */
  context::Context* getSatContext() const;

  /**
   * Get a pointer to the underlying user context.
   */
  context::UserContext* getUserContext() const;

  /**
   * Get a pointer to the underlying quantifiers engine.
   */
  theory::QuantifiersEngine* getQuantifiersEngine() const {
    return d_quantEngine;
  }
  /**
   * Get a pointer to the underlying decision manager.
   */
  theory::DecisionManager* getDecisionManager() const
  {
    return d_decManager.get();
  }

 private:
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
   * Assert the formula to the given theory.
   * @param assertion the assertion to send (not necesserily normalized)
   * @param original the assertion as it was sent in from the propagating theory
   * @param toTheoryId the theory to assert to
   * @param fromTheoryId the theory that sent it
   */
  void assertToTheory(TNode assertion, TNode originalAssertion, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId);

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
  bool markPropagation(TNode assertion, TNode originalAssertions, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId);

  /**
   * Computes the explanation by traversing the propagation graph and
   * asking relevant theories to explain the propagations. Initially
   * the explanation vector should contain only the element (node, theory)
   * where the node is the one to be explained, and the theory is the
   * theory that sent the literal.
   */
  theory::TrustNode getExplanation(
      std::vector<NodeTheoryPair>& explanationVector);

  /** Are proofs enabled? */
  bool isProofEnabled() const;

 public:
  /**
   * Preprocess rewrite equality, called by the preprocessor to rewrite
   * equalities appearing in the input.
   */
  theory::TrustNode ppRewriteEquality(TNode eq);
  /** Notify (preprocessed) assertions. */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);

  /** Return whether or not we are incomplete (in the current context). */
  inline bool isIncomplete() const { return d_incomplete; }

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
  inline bool needCheck() const {
    return d_outputChannelUsed || d_lemmasAdded;
  }
  /**
   * Is the literal lit (possibly) critical for satisfying the input formula in
   * the current context? This call is applicable only during collectModelInfo
   * or during LAST_CALL effort.
   */
  bool isRelevant(Node lit) const;
  /**
   * This is called at shutdown time by the SmtEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory.
   */
  void shutdown();

  /**
   * Solve the given literal with a theory that owns it. The proof of tliteral
   * is carried in the trust node. The proof added to substitutionOut should
   * take this proof into account (when proofs are enabled).
   */
  theory::Theory::PPAssertStatus solve(
      theory::TrustNode tliteral,
      theory::TrustSubstitutionMap& substitutionOut);

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
   * Calls postsolve() on all theories.
   */
  void postsolve();

  /**
   * Calls notifyRestart() on all active theories.
   */
  void notifyRestart();

  void getPropagatedLiterals(std::vector<TNode>& literals) {
    for (; d_propagatedLiteralsIndex < d_propagatedLiterals.size(); d_propagatedLiteralsIndex = d_propagatedLiteralsIndex + 1) {
      Debug("getPropagatedLiterals") << "TheoryEngine::getPropagatedLiterals: propagating: " << d_propagatedLiterals[d_propagatedLiteralsIndex] << std::endl;
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
  theory::TrustNode getExplanation(TNode node);

  /**
   * Get the pointer to the model object used by this theory engine.
   */
  theory::TheoryModel* getModel();
  /**
   * Get the current model for the current set of assertions. This method
   * should only be called immediately after a satisfiable or unknown
   * response to a check-sat call, and only if produceModels is true.
   *
   * If the model is not already built, this will cause this theory engine
   * to build the model.
   *
   * If the model is not available (for instance, if the last call to check-sat
   * was interrupted), then this returns the null pointer.
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
  /** set eager model building
   *
   * If this method is called, then this TheoryEngine will henceforth build
   * its model immediately after every satisfiability check that results
   * in a satisfiable or unknown result. The motivation for this mode is to
   * accomodate API users that get the model object from the TheoryEngine,
   * where we want to ensure that this model is always valid.
   * TODO (#2648): revisit this.
   */
  void setEagerModelBuilding() { d_eager_model_building = true; }

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(TNode node) const {
    return d_theoryTable[theory::Theory::theoryOf(node)];
  }

  /**
   * Get the theory associated to a the given theory id.
   *
   * @returns the theory
   */
  inline theory::Theory* theoryOf(theory::TheoryId theoryId) const {
    Assert(theoryId < theory::THEORY_LAST);
    return d_theoryTable[theoryId];
  }

  inline bool isTheoryEnabled(theory::TheoryId theoryId) const {
    return d_logicInfo.isTheoryEnabled(theoryId);
  }
  /** get the logic info used by this theory engine */
  const LogicInfo& getLogicInfo() const;
  /** get the separation logic heap types */
  bool getSepHeapTypes(TypeNode& locType, TypeNode& dataType) const;

  /**
   * Declare heap. This is used for separation logics to set the location
   * and data types. It should be called only once, and before any separation
   * logic constraints are asserted to this theory engine.
   */
  void declareSepHeap(TypeNode locT, TypeNode dataT);

  /**
   * Returns the equality status of the two terms, from the theory
   * that owns the domain type.  The types of a and b must be the same.
   */
  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Returns the value that a theory that owns the type of var currently
   * has (or null if none);
   */
  Node getModelValue(TNode var);

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
  const std::unordered_set<TNode>& getRelevantAssertions(bool& success);

  /**
   * Forwards an entailment check according to the given theoryOfMode.
   * See theory.h for documentation on entailmentCheck().
   */
  std::pair<bool, Node> entailmentCheck(options::TheoryOfMode mode, TNode lit);

  //---------------------- information about cardinality of types
  /**
   * Is the cardinality of type tn finite? This method depends on whether
   * finite model finding is enabled. If finite model finding is enabled, then
   * we assume that all uninterpreted sorts have finite cardinality.
   *
   * Notice that if finite model finding is enabled, this method returns true
   * if tn is an uninterpreted sort. It also returns true for the sort
   * (Array Int U) where U is an uninterpreted sort. This type
   * is finite if and only if U has cardinality one; for cases like this,
   * we conservatively return that tn has finite cardinality.
   *
   * This method does *not* depend on the state of the theory engine, e.g.
   * if U in the above example currently is entailed to have cardinality >1
   * based on the assertions.
   */
  bool isFiniteType(TypeNode tn) const;
  //---------------------- end information about cardinality of types
 private:

  /** Dump the assertions to the dump */
  void dumpAssertions(const char* tag);

  /** For preprocessing pass lifting bit-vectors of size 1 to booleans */
public:
 theory::SortInference* getSortInference() { return d_sortInfer.get(); }

 /** Prints the assertions to the debug stream */
 void printAssertions(const char* tag);

private:

  std::map< std::string, std::vector< theory::Theory* > > d_attr_handle;

 public:
  /** Set user attribute.
   *
   * This function is called when an attribute is set by a user.  In SMT-LIBv2
   * this is done via the syntax (! n :attr)
   */
  void setUserAttribute(const std::string& attr,
                        Node n,
                        const std::vector<Node>& node_values,
                        const std::string& str_value);

  /** Handle user attribute.
   *
   * Associates theory t with the attribute attr.  Theory t will be
   * notified whenever an attribute of name attr is set.
   */
  void handleUserAttribute(const char* attr, theory::Theory* t);

  /**
   * Check that the theory assertions are satisfied in the model.
   * This function is called from the smt engine's checkModel routine.
   */
  void checkTheoryAssertionsWithModel(bool hardFailure);
};/* class TheoryEngine */

}  // namespace cvc5

#endif /* CVC5__THEORY_ENGINE_H */
