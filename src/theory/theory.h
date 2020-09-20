/*********************                                                        */
/*! \file theory.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base of the theory interface.
 **
 ** Base of the theory interface.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_H
#define CVC4__THEORY__THEORY_H

#include <iosfwd>
#include <map>
#include <set>
#include <string>
#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "options/options.h"
#include "options/theory_options.h"
#include "smt/logic_request.h"
#include "theory/assertion.h"
#include "theory/care_graph.h"
#include "theory/decision_manager.h"
#include "theory/ee_setup_info.h"
#include "theory/logic_info.h"
#include "theory/output_channel.h"
#include "theory/theory_id.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_rewriter.h"
#include "theory/theory_state.h"
#include "theory/trust_node.h"
#include "theory/valuation.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class TheoryEngine;
class ProofNodeManager;

namespace theory {

class QuantifiersEngine;
class TheoryModel;
class SubstitutionMap;
class TheoryRewriter;

namespace rrinst {
  class CandidateGenerator;
}/* CVC4::theory::rrinst namespace */

namespace eq {
  class EqualityEngine;
}/* CVC4::theory::eq namespace */

/**
 * Base class for T-solvers.  Abstract DPLL(T).
 *
 * This is essentially an interface class.  The TheoryEngine has
 * pointers to Theory.  Note that only one specific Theory type (e.g.,
 * TheoryUF) can exist per NodeManager, because of how the
 * RegisteredAttr works.  (If you need multiple instances of the same
 * theory, you'll have to write a multiplexed theory that dispatches
 * all calls to them.)
 *
 * NOTE: A Theory has a special way of being initialized. The owner of a Theory
 * is either:
 *
 * (A) Using Theory as a standalone object, not associated with a TheoryEngine.
 * In this case, simply call the public initialization method
 * (Theory::finishInitStandalone).
 *
 * (B) TheoryEngine, which determines how the Theory acts in accordance with
 * its theory combination policy. We require the following steps in order:
 * (B.1) Get information about whether the theory wishes to use an equality
 * eninge, and more specifically which equality engine notifications the Theory
 * would like to be notified of (Theory::needsEqualityEngine).
 * (B.2) Set the equality engine of the theory (Theory::setEqualityEngine),
 * which we refer to as the "official equality engine" of this Theory. The
 * equality engine passed to the theory must respect the contract(s) specified
 * by the equality engine setup information (EeSetupInfo) returned in the
 * previous step.
 * (B.3) Set the other required utilities including setQuantifiersEngine and
 * setDecisionManager.
 * (B.4) Call the private initialization method (Theory::finishInit).
 *
 * Initialization of the second form happens during TheoryEngine::finishInit,
 * after the quantifiers engine and model objects have been set up.
 */
class Theory {
  friend class ::CVC4::TheoryEngine;

 private:
  // Disallow default construction, copy, assignment.
  Theory() = delete;
  Theory(const Theory&) = delete;
  Theory& operator=(const Theory&) = delete;

  /** An integer identifying the type of the theory. */
  TheoryId d_id;

  /** The SAT search context for the Theory. */
  context::Context* d_satContext;

  /** The user level assertion context for the Theory. */
  context::UserContext* d_userContext;

  /** Information about the logic we're operating within. */
  const LogicInfo& d_logicInfo;

  /** Pointer to proof node manager */
  ProofNodeManager* d_pnm;

  /**
   * The assertFact() queue.
   *
   * These can not be TNodes as some atoms (such as equalities) are sent
   * across theories without being stored in a global map.
   */
  context::CDList<Assertion> d_facts;

  /** Index into the head of the facts list */
  context::CDO<unsigned> d_factsHead;

  /** Indices for splitting on the shared terms. */
  context::CDO<unsigned> d_sharedTermsIndex;

  /** The care graph the theory will use during combination. */
  CareGraph* d_careGraph;

  /**
   * Pointer to the quantifiers engine (or NULL, if quantifiers are not
   * supported or not enabled). Not owned by the theory.
   */
  QuantifiersEngine* d_quantEngine;

  /** Pointer to the decision manager. */
  DecisionManager* d_decManager;

 protected:
  /** Name of this theory instance. Along with the TheoryId this should provide
   * an unique string identifier for each instance of a Theory class. We need
   * this to ensure unique statistics names over multiple theory instances. */
  std::string d_instanceName;

  // === STATISTICS ===
  /** time spent in check calls */
  TimerStat d_checkTime;
  /** time spent in theory combination */
  TimerStat d_computeCareGraphTime;

  /**
   * The only method to add suff to the care graph.
   */
  void addCarePair(TNode t1, TNode t2);

  /**
   * The function should compute the care graph over the shared terms.
   * The default function returns all the pairs among the shared variables.
   */
  virtual void computeCareGraph();

  /**
   * A list of shared terms that the theory has.
   */
  context::CDList<TNode> d_sharedTerms;

  //---------------------------------- private collect model info
  /**
   * Helper function for computeRelevantTerms
   */
  void collectTerms(TNode n,
                    const std::set<Kind>& irrKinds,
                    std::set<Node>& termSet) const;
  //---------------------------------- end private collect model info

  /**
   * Construct a Theory.
   *
   * The pair <id, instance> is assumed to uniquely identify this Theory
   * w.r.t. the SmtEngine.
   */
  Theory(TheoryId id,
         context::Context* satContext,
         context::UserContext* userContext,
         OutputChannel& out,
         Valuation valuation,
         const LogicInfo& logicInfo,
         ProofNodeManager* pnm,
         std::string instance = "");  // taking : No default.

  /**
   * This is called at shutdown time by the TheoryEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory (based on what
   * hard-links to Nodes are outstanding).  As the fact queue might be
   * nonempty, we ensure here that it's clear.  If you overload this,
   * you must make an explicit call here to this->Theory::shutdown()
   * too.
   */
  virtual void shutdown() { }

  /**
   * The output channel for the Theory.
   */
  OutputChannel* d_out;

  /**
   * The valuation proxy for the Theory to communicate back with the
   * theory engine (and other theories).
   */
  Valuation d_valuation;
  /**
   * Pointer to the official equality engine of this theory, which is owned by
   * the equality engine manager of TheoryEngine.
   */
  eq::EqualityEngine* d_equalityEngine;
  /**
   * The official equality engine, if we allocated it.
   */
  std::unique_ptr<eq::EqualityEngine> d_allocEqualityEngine;
  /**
   * The theory state, which contains contexts, valuation, and equality engine.
   * Notice the theory is responsible for memory management of this class.
   */
  TheoryState* d_theoryState;
  /**
   * The theory inference manager. This is a wrapper around the equality
   * engine and the output channel. It ensures that the output channel and
   * the equality engine are used properly.
   */
  TheoryInferenceManager* d_inferManager;

  /**
   * Returns the next assertion in the assertFact() queue.
   *
   * @return the next assertion in the assertFact() queue
   */
  inline Assertion get();

  const LogicInfo& getLogicInfo() const {
    return d_logicInfo;
  }

  /**
   * The theory that owns the uninterpreted sort.
   */
  static TheoryId s_uninterpretedSortOwner;

  void printFacts(std::ostream& os) const;
  void debugPrintFacts() const;

  /** is legal elimination
   *
   * Returns true if x -> val is a legal elimination of variable x. This is
   * useful for ppAssert, when x = val is an entailed equality. This function
   * determines whether indeed x can be eliminated from the problem via the
   * substituion x -> val.
   *
   * The following criteria imply that x -> val is *not* a legal elimination:
   * (1) If x is contained in val,
   * (2) If the type of val is not a subtype of the type of x,
   * (3) If val contains an operator that cannot be evaluated, and produceModels
   * is true. For example, x -> sqrt(2) is not a legal elimination if we
   * are producing models. This is because we care about the value of x, and
   * its value must be computed (approximated) by the non-linear solver.
   */
  bool isLegalElimination(TNode x, TNode val);
  //--------------------------------- private initialization
  /**
   * Called to set the official equality engine. This should be done by
   * TheoryEngine only.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
  /** Called to set the quantifiers engine. */
  void setQuantifiersEngine(QuantifiersEngine* qe);
  /** Called to set the decision manager. */
  void setDecisionManager(DecisionManager* dm);
  /**
   * Finish theory initialization.  At this point, options and the logic
   * setting are final, the master equality engine and quantifiers
   * engine (if any) are initialized, and the official equality engine of this
   * theory has been assigned.  This base class implementation
   * does nothing. This should be called by TheoryEngine only.
   */
  virtual void finishInit() {}
  //--------------------------------- end private initialization

  /**
   * This method is called to notify a theory that the node n should
   * be considered a "shared term" by this theory. This does anything
   * theory-specific concerning the fact that n is now marked as a shared
   * term, which is done in addition to explicitly storing n as a shared
   * term and adding it as a trigger term in the equality engine of this
   * class (see addSharedTerm).
   */
  virtual void notifySharedTerm(TNode n);

 public:
  //--------------------------------- initialization
  /**
   * @return The theory rewriter associated with this theory.
   */
  virtual TheoryRewriter* getTheoryRewriter() = 0;
  /**
   * Returns true if this theory needs an equality engine for checking
   * satisfiability.
   *
   * If this method returns true, then the equality engine manager will
   * initialize its equality engine field via setEqualityEngine above during
   * TheoryEngine::finishInit, prior to calling finishInit for this theory.
   *
   * Additionally, if this method returns true, then this method is required to
   * update the argument esi with instructions for initializing and setting up
   * notifications from its equality engine, which is commonly done with
   * a notifications class (eq::EqualityEngineNotify).
   */
  virtual bool needsEqualityEngine(EeSetupInfo& esi);
  /**
   * Finish theory initialization, standalone version. This is used to
   * initialize this class if it is not associated with a theory engine.
   * This allocates the official equality engine of this Theory and then
   * calls the finishInit method above.
   */
  void finishInitStandalone();
  //--------------------------------- end initialization

  /**
   * Return the ID of the theory responsible for the given type.
   */
  static inline TheoryId theoryOf(TypeNode typeNode) {
    Trace("theory::internal") << "theoryOf(" << typeNode << ")" << std::endl;
    TheoryId id;
    if (typeNode.getKind() == kind::TYPE_CONSTANT) {
      id = typeConstantToTheoryId(typeNode.getConst<TypeConstant>());
    } else {
      id = kindToTheoryId(typeNode.getKind());
    }
    if (id == THEORY_BUILTIN) {
      Trace("theory::internal") << "theoryOf(" << typeNode << ") == " << s_uninterpretedSortOwner << std::endl;
      return s_uninterpretedSortOwner;
    }
    return id;
  }

  /**
   * Returns the ID of the theory responsible for the given node.
   */
  static TheoryId theoryOf(options::TheoryOfMode mode, TNode node);

  /**
   * Returns the ID of the theory responsible for the given node.
   */
  static inline TheoryId theoryOf(TNode node) {
    return theoryOf(options::theoryOfMode(), node);
  }

  /**
   * Set the owner of the uninterpreted sort.
   */
  static void setUninterpretedSortOwner(TheoryId theory) {
    s_uninterpretedSortOwner = theory;
  }

  /**
   * Get the owner of the uninterpreted sort.
   */
  static TheoryId getUninterpretedSortOwner() {
    return s_uninterpretedSortOwner;
  }

  /**
   * Checks if the node is a leaf node of this theory
   */
  inline bool isLeaf(TNode node) const {
    return node.getNumChildren() == 0 || theoryOf(node) != d_id;
  }

  /**
   * Checks if the node is a leaf node of a theory.
   */
  inline static bool isLeafOf(TNode node, TheoryId theoryId) {
    return node.getNumChildren() == 0 || theoryOf(node) != theoryId;
  }

  /** Returns true if the assertFact queue is empty*/
  bool done() const { return d_factsHead == d_facts.size(); }
  /**
   * Destructs a Theory.
   */
  virtual ~Theory();

  /**
   * Subclasses of Theory may add additional efforts.  DO NOT CHECK
   * equality with one of these values (e.g. if STANDARD xxx) but
   * rather use range checks (or use the helper functions below).
   * Normally we call QUICK_CHECK or STANDARD; at the leaves we call
   * with FULL_EFFORT.
   */
  enum Effort
  {
    /**
     * Standard effort where theory need not do anything
     */
    EFFORT_STANDARD = 50,
    /**
     * Full effort requires the theory make sure its assertions are satisfiable
     * or not
     */
    EFFORT_FULL = 100,
    /**
     * Last call effort, called after theory combination has completed with
     * no lemmas and a model is available.
     */
    EFFORT_LAST_CALL = 200
  }; /* enum Effort */

  static inline bool standardEffortOrMore(Effort e) CVC4_CONST_FUNCTION
    { return e >= EFFORT_STANDARD; }
  static inline bool standardEffortOnly(Effort e) CVC4_CONST_FUNCTION
    { return e >= EFFORT_STANDARD && e <  EFFORT_FULL; }
  static inline bool fullEffort(Effort e) CVC4_CONST_FUNCTION
    { return e == EFFORT_FULL; }

  /**
   * Get the id for this Theory.
   */
  TheoryId getId() const {
    return d_id;
  }

  /**
   * Get the SAT context associated to this Theory.
   */
  context::Context* getSatContext() const {
    return d_satContext;
  }

  /**
   * Get the context associated to this Theory.
   */
  context::UserContext* getUserContext() const {
    return d_userContext;
  }

  /**
   * Set the output channel associated to this theory.
   */
  void setOutputChannel(OutputChannel& out) {
    d_out = &out;
  }

  /**
   * Get the output channel associated to this theory.
   */
  OutputChannel& getOutputChannel() {
    return *d_out;
  }

  /**
   * Get the valuation associated to this theory.
   */
  Valuation& getValuation() {
    return d_valuation;
  }

  /** Get the equality engine being used by this theory. */
  eq::EqualityEngine* getEqualityEngine();

  /**
   * Get the quantifiers engine associated to this theory.
   */
  QuantifiersEngine* getQuantifiersEngine() {
    return d_quantEngine;
  }

  /** Get the decision manager associated to this theory. */
  DecisionManager* getDecisionManager() { return d_decManager; }

  /**
   * Expand definitions in the term node. This returns a term that is
   * equivalent to node. It wraps this term in a TrustNode of kind
   * TrustNodeKind::REWRITE. If node is unchanged by this method, the
   * null TrustNode may be returned. This is an optimization to avoid
   * constructing the trivial equality (= node node) internally within
   * TrustNode.
   *
   * The purpose of this method is typically to eliminate the operators in node
   * that are syntax sugar that cannot otherwise be eliminated during rewriting.
   * For example, division relies on the introduction of an uninterpreted
   * function for the divide-by-zero case, which we do not introduce with
   * the rewriter, since this function may be cached in a non-global fashion.
   *
   * Some theories have kinds that are effectively definitions and should be
   * expanded before they are handled.  Definitions allow a much wider range of
   * actions than the normal forms given by the rewriter. However no
   * assumptions can be made about subterms having been expanded or rewritten.
   * Where possible rewrite rules should be used, definitions should only be
   * used when rewrites are not possible, for example in handling
   * under-specified operations using partially defined functions.
   *
   * Some theories like sets use expandDefinition as a "context
   * independent preRegisterTerm".  This is required for cases where
   * a theory wants to be notified about a term before preprocessing
   * and simplification but doesn't necessarily want to rewrite it.
   */
  virtual TrustNode expandDefinition(Node node)
  {
    // by default, do nothing
    return TrustNode::null();
  }

  /**
   * Pre-register a term.  Done one time for a Node per SAT context level.
   */
  virtual void preRegisterTerm(TNode);

  /**
   * Assert a fact in the current context.
   */
  void assertFact(TNode assertion, bool isPreregistered) {
    Trace("theory") << "Theory<" << getId() << ">::assertFact["
                    << d_satContext->getLevel() << "](" << assertion << ", "
                    << (isPreregistered ? "true" : "false") << ")" << std::endl;
    d_facts.push_back(Assertion(assertion, isPreregistered));
  }

  /** Add shared term to the theory. */
  void addSharedTerm(TNode node);

  /**
   * Return the current theory care graph. Theories should overload
   * computeCareGraph to do the actual computation, and use addCarePair to add
   * pairs to the care graph.
   */
  void getCareGraph(CareGraph* careGraph);

  /**
   * Return the status of two terms in the current context. Should be
   * implemented in sub-theories to enable more efficient theory-combination.
   */
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Return the model value of the give shared term (or null if not available).
   *
   * TODO (project #39): this method is likely to become deprecated.
   */
  virtual Node getModelValue(TNode var) { return Node::null(); }

  /** T-propagate new literal assignments in the current context. */
  virtual void propagate(Effort level = EFFORT_FULL) {}

  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).
   */
  virtual TrustNode explain(TNode n)
  {
    Unimplemented() << "Theory " << identify()
                    << " propagated a node but doesn't implement the "
                       "Theory::explain() interface!";
    return TrustNode::null();
  }

  //--------------------------------- check
  /**
   * Does this theory wish to be called to check at last call effort? This is
   * the case for any theory that wishes to run when a model is available.
   */
  virtual bool needsCheckLastEffort() { return false; }
  /**
   * Check the current assignment's consistency.
   *
   * An implementation of check() is required to either:
   * - return a conflict on the output channel,
   * - be interrupted,
   * - throw an exception
   * - or call get() until done() is true.
   *
   * The standard method for check consists of a loop that processes the entire
   * fact queue when preCheck returns false. It makes four theory-specific
   * callbacks, (preCheck, postCheck, preNotifyFact, notifyFact) as described
   * below. It asserts each fact to the official equality engine when
   * preNotifyFact returns false.
   *
   * Theories that use this check method must use an official theory
   * state object (d_theoryState).
   *
   * TODO (project #39): this method should be non-virtual, once all theories
   * conform to the new standard
   */
  virtual void check(Effort level = EFFORT_FULL);
  /**
   * Pre-check, called before the fact queue of the theory is processed.
   * If this method returns false, then the theory will process its fact
   * queue. If this method returns true, then the theory has indicated
   * its check method should finish immediately.
   */
  virtual bool preCheck(Effort level = EFFORT_FULL);
  /**
   * Post-check, called after the fact queue of the theory is processed.
   */
  virtual void postCheck(Effort level = EFFORT_FULL);
  /**
   * Pre-notify fact, return true if the theory processed it. If this
   * method returns false, then the atom will be added to the equality engine
   * of the theory and notifyFact will be called with isInternal=false.
   *
   * Theories that implement check but do not use official equality
   * engines should always return true for this method.
   *
   * @param atom The atom
   * @param polarity Its polarity
   * @param fact The original literal that was asserted
   * @param isPrereg Whether the assertion is preregistered
   * @param isInternal Whether the origin of the fact was internal. If this
   * is false, the fact was asserted via the fact queue of the theory.
   * @return true if the theory completely processed this fact, i.e. it does
   * not need to assert the fact to its equality engine.
   */
  virtual bool preNotifyFact(
      TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal);
  /**
   * Notify fact, called immediately after the fact was pushed into the
   * equality engine.
   *
   * @param atom The atom
   * @param polarity Its polarity
   * @param fact The original literal that was asserted.
   * @param isInternal Whether the origin of the fact was internal. If this
   * is false, the fact was asserted via the fact queue of the theory.
   */
  virtual void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal);
  //--------------------------------- end check

  //--------------------------------- collect model info
  /**
   * Get all relevant information in this theory regarding the current
   * model.  This should be called after a call to check( FULL_EFFORT )
   * for all theories with no conflicts and no lemmas added.
   *
   * This method returns true if and only if the equality engine of m is
   * consistent as a result of this call.
   *
   * The standard method for collectModelInfo computes the relevant terms,
   * asserts the theory's equality engine to the model (if necessary) and
   * then calls computeModelValues.
   *
   * TODO (project #39): this method should be non-virtual, once all theories
   * conform to the new standard
   */
  virtual bool collectModelInfo(TheoryModel* m);
  /**
   * Scans the current set of assertions and shared terms top-down
   * until a theory-leaf is reached, and adds all terms found to
   * termSet.  This is used by collectModelInfo to delimit the set of
   * terms that should be used when constructing a model.
   *
   * @param irrKinds The kinds of terms that appear in assertions that should *not*
   * be included in termSet. Note that the kinds EQUAL and NOT are always
   * treated as irrelevant kinds.
   *
   * @param includeShared Whether to include shared terms in termSet. Notice that
   * shared terms are not influenced by irrKinds.
   *
   * TODO (project #39): this method will be deleted. The version in
   * model manager will be used.
   */
  void computeAssertedTerms(std::set<Node>& termSet,
                            const std::set<Kind>& irrKinds,
                            bool includeShared = true) const;
  /**
   * Compute terms that are not necessarily part of the assertions or
   * shared terms that should be considered relevant, add them to termSet.
   */
  virtual void computeRelevantTerms(std::set<Node>& termSet);
  /**
   * Collect model values, after equality information is added to the model.
   * The argument termSet is the set of relevant terms returned by
   * computeRelevantTerms.
   */
  virtual bool collectModelValues(TheoryModel* m,
                                  const std::set<Node>& termSet);
  /** if theories want to do something with model after building, do it here */
  virtual void postProcessModel( TheoryModel* m ){ }
  //--------------------------------- end collect model info

  //--------------------------------- preprocessing
  /**
   * Statically learn from assertion "in," which has been asserted
   * true at the top level.  The theory should only add (via
   * ::operator<< or ::append()) to the "learned" builder---it should
   * *never* clear it.  It is a conjunction to add to the formula at
   * the top-level and may contain other theories' contributions.
   */
  virtual void ppStaticLearn(TNode in, NodeBuilder<>& learned) { }

  enum PPAssertStatus {
    /** Atom has been solved  */
    PP_ASSERT_STATUS_SOLVED,
    /** Atom has not been solved */
    PP_ASSERT_STATUS_UNSOLVED,
    /** Atom is inconsistent */
    PP_ASSERT_STATUS_CONFLICT
  };

  /**
   * Given a literal, add the solved substitutions to the map, if any.
   * The method should return true if the literal can be safely removed.
   */
  virtual PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);

  /**
   * Given an atom of the theory coming from the input formula, this
   * method can be overridden in a theory implementation to rewrite
   * the atom into an equivalent form.  This is only called just
   * before an input atom to the engine. This method returns a TrustNode of
   * kind TrustNodeKind::REWRITE, which carries information about the proof
   * generator for the rewrite. Similarly to expandDefinition, this method may
   * return the null TrustNode if atom is unchanged.
   */
  virtual TrustNode ppRewrite(TNode atom) { return TrustNode::null(); }

  /**
   * Notify preprocessed assertions. Called on new assertions after
   * preprocessing before they are asserted to theory engine.
   */
  virtual void ppNotifyAssertions(const std::vector<Node>& assertions) {}
  //--------------------------------- end preprocessing

  /**
   * A Theory is called with presolve exactly one time per user
   * check-sat.  presolve() is called after preregistration,
   * rewriting, and Boolean propagation, (other theories'
   * propagation?), but the notified Theory has not yet had its
   * check() or propagate() method called.  A Theory may empty its
   * assertFact() queue using get().  A Theory can raise conflicts,
   * add lemmas, and propagate literals during presolve().
   *
   * NOTE: The presolve property must be added to the kinds file for
   * the theory.
   */
  virtual void presolve() { }

  /**
   * A Theory is called with postsolve exactly one time per user
   * check-sat.  postsolve() is called after the query has completed
   * (regardless of whether sat, unsat, or unknown), and after any
   * model-querying related to the query has been performed.
   * After this call, the theory will not get another check() or
   * propagate() call until presolve() is called again.  A Theory
   * cannot raise conflicts, add lemmas, or propagate literals during
   * postsolve().
   */
  virtual void postsolve() { }

  /**
   * Notification sent to the theory wheneven the search restarts.
   * Serves as a good time to do some clean-up work, and you can
   * assume you're at DL 0 for the purposes of Contexts.  This function
   * should not use the output channel.
   */
  virtual void notifyRestart() { }

  /**
   * Identify this theory (for debugging, dynamic configuration,
   * etc..)
   */
  virtual std::string identify() const = 0;

  /** Set user attribute
    * This function is called when an attribute is set by a user.  In SMT-LIBv2 this is done
    *  via the syntax (! n :attr)
    */
  virtual void setUserAttribute(const std::string& attr, Node n, std::vector<Node> node_values, std::string str_value) {
    Unimplemented() << "Theory " << identify()
                    << " doesn't support Theory::setUserAttribute interface";
  }

  typedef context::CDList<Assertion>::const_iterator assertions_iterator;

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the beginning of the fact queue
   */
  assertions_iterator facts_begin() const {
    return d_facts.begin();
  }

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the end of the fact queue
   */
  assertions_iterator facts_end() const {
    return d_facts.end();
  }
  /**
   * Whether facts have been asserted to this theory.
   *
   * @return true iff facts have been asserted to this theory.
   */
  bool hasFacts() { return !d_facts.empty(); }

  /** Return total number of facts asserted to this theory */
  size_t numAssertions() {
    return d_facts.size();
  }

  typedef context::CDList<TNode>::const_iterator shared_terms_iterator;

  /**
   * Provides access to the shared terms, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the beginning of the shared terms list
   */
  shared_terms_iterator shared_terms_begin() const {
    return d_sharedTerms.begin();
  }

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the end of the shared terms list
   */
  shared_terms_iterator shared_terms_end() const {
    return d_sharedTerms.end();
  }


  /**
   * This is a utility function for constructing a copy of the currently shared terms
   * in a queriable form.  As this is
   */
  std::unordered_set<TNode, TNodeHashFunction> currentlySharedTerms() const;

  /**
   * This allows the theory to be queried for whether a literal, lit, is
   * entailed by the theory.  This returns a pair of a Boolean and a node E.
   *
   * If the Boolean is true, then E is a formula that entails lit and E is propositionally
   * entailed by the assertions to the theory.
   *
   * If the Boolean is false, it is "unknown" if lit is entailed and E may be
   * any node.
   *
   * The literal lit is either an atom a or (not a), which must belong to the theory:
   *   There is some TheoryOfMode m s.t. Theory::theoryOf(m, a) == this->getId().
   *
   * There are NO assumptions that a or the subterms of a have been
   * preprocessed in any form.  This includes ppRewrite, rewriting,
   * preregistering, registering, definition expansion or ITE removal!
   *
   * Theories are free to limit the amount of effort they use and so may
   * always opt to return "unknown".  Both "unknown" and "not entailed",
   * may return for E a non-boolean Node (e.g. Node::null()).  (There is no explicit output
   * for the negation of lit is entailed.)
   *
   * If lit is theory valid, the return result may be the Boolean constant
   * true for E.
   *
   * If lit is entailed by multiple assertions on the theory's getFact()
   * queue, a_1, a_2, ... and a_k, this may return E=(and a_1 a_2 ... a_k) or
   * another theory entailed explanation E=(and (and a_1 a_2) (and a3 a_4) ... a_k)
   *
   * If lit is entailed by a single assertion on the theory's getFact()
   * queue, say a, this may return E=a.
   *
   * The theory may always return false!
   *
   * Theories may not touch their output stream during an entailment check.
   *
   * @param  lit     a literal belonging to the theory.
   * @return         a pair <b,E> s.t. if b is true, then a formula E such that
   * E |= lit in the theory.
   */
  virtual std::pair<bool, Node> entailmentCheck(TNode lit);
};/* class Theory */

std::ostream& operator<<(std::ostream& os, theory::Theory::Effort level);


inline theory::Assertion Theory::get() {
  Assert(!done()) << "Theory::get() called with assertion queue empty!";

  // Get the assertion
  Assertion fact = d_facts[d_factsHead];
  d_factsHead = d_factsHead + 1;

  Trace("theory") << "Theory::get() => " << fact << " (" << d_facts.size() - d_factsHead << " left)" << std::endl;

  return fact;
}

inline std::ostream& operator<<(std::ostream& out,
                                const CVC4::theory::Theory& theory) {
  return out << theory.identify();
}

inline std::ostream& operator << (std::ostream& out, theory::Theory::PPAssertStatus status) {
  switch (status) {
  case theory::Theory::PP_ASSERT_STATUS_SOLVED:
    out << "SOLVE_STATUS_SOLVED"; break;
  case theory::Theory::PP_ASSERT_STATUS_UNSOLVED:
    out << "SOLVE_STATUS_UNSOLVED"; break;
  case theory::Theory::PP_ASSERT_STATUS_CONFLICT:
    out << "SOLVE_STATUS_CONFLICT"; break;
  default:
    Unhandled();
  }
  return out;
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__THEORY_H */
