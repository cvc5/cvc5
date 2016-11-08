/*********************                                                        */
/*! \file theory.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base of the theory interface.
 **
 ** Base of the theory interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__THEORY_H
#define __CVC4__THEORY__THEORY_H

#include <ext/hash_set>
#include <iosfwd>
#include <string>

#include "context/cdlist.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "lib/ffs.h"
#include "options/options.h"
#include "options/theory_options.h"
#include "options/theoryof_mode.h"
#include "smt/command.h"
#include "smt/dump.h"
#include "smt/logic_request.h"
#include "theory/logic_info.h"
#include "theory/output_channel.h"
#include "theory/valuation.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

class QuantifiersEngine;
class TheoryModel;
class SubstitutionMap;
class ExtTheory;

class EntailmentCheckParameters;
class EntailmentCheckSideEffects;

namespace rrinst {
  class CandidateGenerator;
}/* CVC4::theory::rrinst namespace */

namespace eq {
  class EqualityEngine;
}/* CVC4::theory::eq namespace */

/**
 * Information about an assertion for the theories.
 */
struct Assertion {

  /** The assertion */
  Node assertion;
  /** Has this assertion been preregistered with this theory */
  bool isPreregistered;

  Assertion(TNode assertion, bool isPreregistered)
  : assertion(assertion), isPreregistered(isPreregistered) {}

  /**
   * Convert the assertion to a TNode.
   */
  operator TNode () const {
    return assertion;
  }

  /**
   * Convert the assertion to a Node.
   */
  operator Node () const {
    return assertion;
  }

};/* struct Assertion */

/**
 * A (oredered) pair of terms a theory cares about.
 */
struct CarePair {

  TNode a, b;
  TheoryId theory;

public:

  CarePair(TNode a, TNode b, TheoryId theory)
  : a(a < b ? a : b), b(a < b ? b : a), theory(theory) {}

  bool operator == (const CarePair& other) const {
    return (theory == other.theory) && (a == other.a) && (b == other.b);
  }

  bool operator < (const CarePair& other) const {
    if (theory < other.theory) return true;
    if (theory > other.theory) return false;
    if (a < other.a) return true;
    if (a > other.a) return false;
    return b < other.b;
  }

};/* struct CarePair */

/**
 * A set of care pairs.
 */
typedef std::set<CarePair> CareGraph;

/**
 * Base class for T-solvers.  Abstract DPLL(T).
 *
 * This is essentially an interface class.  The TheoryEngine has
 * pointers to Theory.  Note that only one specific Theory type (e.g.,
 * TheoryUF) can exist per NodeManager, because of how the
 * RegisteredAttr works.  (If you need multiple instances of the same
 * theory, you'll have to write a multiplexed theory that dispatches
 * all calls to them.)
 */
class Theory {

private:

  friend class ::CVC4::TheoryEngine;

  // Disallow default construction, copy, assignment.
  Theory() CVC4_UNDEFINED;
  Theory(const Theory&) CVC4_UNDEFINED;
  Theory& operator=(const Theory&) CVC4_UNDEFINED;

  /**
   * An integer identifying the type of the theory
   */
  TheoryId d_id;

  /** Name of this theory instance. Along with the TheoryId this should provide
   * an unique string identifier for each instance of a Theory class. We need
   * this to ensure unique statistics names over multiple theory instances. */
  std::string d_instanceName;

  /**
   * The SAT search context for the Theory.
   */
  context::Context* d_satContext;

  /**
   * The user level assertion context for the Theory.
   */
  context::UserContext* d_userContext;

  /**
   * Information about the logic we're operating within.
   */
  const LogicInfo& d_logicInfo;

  /**
   * The assertFact() queue.
   *
   * These can not be TNodes as some atoms (such as equalities) are sent
   * across theories without being stored in a global map.
   */
  context::CDList<Assertion> d_facts;

  /** Index into the head of the facts list */
  context::CDO<unsigned> d_factsHead;

  /**
   * Add shared term to the theory.
   */
  void addSharedTermInternal(TNode node);

  /**
   * Indices for splitting on the shared terms.
   */
  context::CDO<unsigned> d_sharedTermsIndex;

  /**
   * The care graph the theory will use during combination.
   */
  CareGraph* d_careGraph;

  /**
   * Reference to the quantifiers engine (or NULL, if quantifiers are
   * not supported or not enabled).
   */
  QuantifiersEngine* d_quantEngine;

protected:

  /** extended theory */
  ExtTheory * d_extt;

  // === STATISTICS ===
  /** time spent in check calls */
  TimerStat d_checkTime;
  /** time spent in theory combination */
  TimerStat d_computeCareGraphTime;

  /**
   * The only method to add suff to the care graph.
   */
  void addCarePair(TNode t1, TNode t2) {
    if (d_careGraph) {
      d_careGraph->insert(CarePair(t1, t2, d_id));
    }
  }

  /**
   * The function should compute the care graph over the shared terms.
   * The default function returns all the pairs among the shared variables.
   */
  virtual void computeCareGraph();

  /**
   * A list of shared terms that the theory has.
   */
  context::CDList<TNode> d_sharedTerms;

  /**
   * Helper function for computeRelevantTerms
   */
  void collectTerms(TNode n, std::set<Node>& termSet) const;
  /**
   * Scans the current set of assertions and shared terms top-down
   * until a theory-leaf is reached, and adds all terms found to
   * termSet.  This is used by collectModelInfo to delimit the set of
   * terms that should be used when constructing a model
   */
  void computeRelevantTerms(std::set<Node>& termSet, bool includeShared = true) const;

  /**
   * Construct a Theory.
   *
   * The pair <id, instance> is assumed to uniquely identify this Theory
   * w.r.t. the SmtEngine.
   */
  Theory(TheoryId id, context::Context* satContext,
         context::UserContext* userContext, OutputChannel& out,
         Valuation valuation, const LogicInfo& logicInfo,
         std::string instance = "") throw();  // taking : No default.

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
   * Whether proofs are enabled
   *
   */
  bool d_proofsEnabled;

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

  /**
   * Whether proofs are enabled
   *
   */
  bool d_proofEnabled;

public:

  /**
   * Return the ID of the theory responsible for the given type.
   */
  static inline TheoryId theoryOf(TypeNode typeNode) {
    Trace("theory::internal") << "theoryOf(" << typeNode << ")" << std::endl;
    TheoryId id;
    while (typeNode.isPredicateSubtype()) {
      typeNode = typeNode.getSubtypeParentType();
    }
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
  static TheoryId theoryOf(TheoryOfMode mode, TNode node);

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

  /**
   * Returns true if the assertFact queue is empty
   */
  bool done() const throw() {
    return d_factsHead == d_facts.size();
  }

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
  enum Effort {
    /**
     * Standard effort where theory need not do anything
     */
    EFFORT_STANDARD = 50,
    /**
     * Full effort requires the theory make sure its assertions are satisfiable or not
     */
    EFFORT_FULL = 100,
    /**
     * Combination effort means that the individual theories are already satisfied, and
     * it is time to put some effort into propagation of shared term equalities
     */
    EFFORT_COMBINATION = 150,
    /**
     * Last call effort, reserved for quantifiers.
     */
    EFFORT_LAST_CALL = 200
  };/* enum Effort */

  static inline bool standardEffortOrMore(Effort e) CVC4_CONST_FUNCTION
    { return e >= EFFORT_STANDARD; }
  static inline bool standardEffortOnly(Effort e) CVC4_CONST_FUNCTION
    { return e >= EFFORT_STANDARD && e <  EFFORT_FULL; }
  static inline bool fullEffort(Effort e) CVC4_CONST_FUNCTION
    { return e == EFFORT_FULL; }
  static inline bool combination(Effort e) CVC4_CONST_FUNCTION
    { return e == EFFORT_COMBINATION; }

  /**
   * Get the id for this Theory.
   */
  TheoryId getId() const {
    return d_id;
  }

  /**
   * Returns a string that uniquely identifies this theory solver w.r.t. the
   * SmtEngine.
   */
  std::string getFullInstanceName() const;


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

  /**
   * Get the quantifiers engine associated to this theory.
   */
  QuantifiersEngine* getQuantifiersEngine() {
    return d_quantEngine;
  }

  /**
   * Get the quantifiers engine associated to this theory (const version).
   */
  const QuantifiersEngine* getQuantifiersEngine() const {
    return d_quantEngine;
  }

  /**
   * Finish theory initialization.  At this point, options and the logic
   * setting are final, and the master equality engine and quantifiers
   * engine (if any) are initialized.  This base class implementation
   * does nothing.
   */
  virtual void finishInit() { }

  /**
   * Some theories have kinds that are effectively definitions and
   * should be expanded before they are handled.  Definitions allow
   * a much wider range of actions than the normal forms given by the
   * rewriter; they can enable other theories and create new terms.
   * However no assumptions can be made about subterms having been
   * expanded or rewritten.  Where possible rewrite rules should be
   * used, definitions should only be used when rewrites are not
   * possible, for example in handling under-specified operations
   * using partially defined functions.
   */
  virtual Node expandDefinition(LogicRequest &logicRequest, Node node) {
    // by default, do nothing
    return node;
  }

  /**
   * Pre-register a term.  Done one time for a Node per SAT context level.
   */
  virtual void preRegisterTerm(TNode) { }

  /**
   * Assert a fact in the current context.
   */
  void assertFact(TNode assertion, bool isPreregistered) {
    Trace("theory") << "Theory<" << getId() << ">::assertFact[" << d_satContext->getLevel() << "](" << assertion << ", " << (isPreregistered ? "true" : "false") << ")" << std::endl;
    d_facts.push_back(Assertion(assertion, isPreregistered));
  }

  /**
   * This method is called to notify a theory that the node n should
   * be considered a "shared term" by this theory
   */
  virtual void addSharedTerm(TNode n) { }

  /**
   * Called to set the master equality engine.
   */
  virtual void setMasterEqualityEngine(eq::EqualityEngine* eq) { }

  /**
   * Called to set the quantifiers engine.
   */
  virtual void setQuantifiersEngine(QuantifiersEngine* qe) {
    d_quantEngine = qe;
  }

  /**
   * Return the current theory care graph. Theories should overload computeCareGraph to do
   * the actual computation, and use addCarePair to add pairs to the care graph.
   */
  void getCareGraph(CareGraph& careGraph) {
    Trace("sharing") << "Theory<" << getId() << ">::getCareGraph()" << std::endl;
    TimerStat::CodeTimer computeCareGraphTime(d_computeCareGraphTime);
    d_careGraph = &careGraph;
    computeCareGraph();
    d_careGraph = NULL;
  }

  /**
   * Return the status of two terms in the current context. Should be implemented in
   * sub-theories to enable more efficient theory-combination.
   */
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b) { return EQUALITY_UNKNOWN; }

  /**
   * Return the model value of the give shared term (or null if not available).
   */
  virtual Node getModelValue(TNode var) { return Node::null(); }

  /**
   * Check the current assignment's consistency.
   *
   * An implementation of check() is required to either:
   * - return a conflict on the output channel,
   * - be interrupted,
   * - throw an exception
   * - or call get() until done() is true.
   */
  virtual void check(Effort level = EFFORT_FULL) { }
  
  /**
   * Needs last effort check?
   */ 
  virtual bool needsCheckLastEffort() { return false; }
  /**
   * T-propagate new literal assignments in the current context.
   */
  virtual void propagate(Effort level = EFFORT_FULL) { }

  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).
   */
  virtual Node explain(TNode n) {
    Unimplemented("Theory %s propagated a node but doesn't implement the "
                  "Theory::explain() interface!", identify().c_str());
  }

  /**
   * Get all relevant information in this theory regarding the current
   * model.  This should be called after a call to check( FULL_EFFORT )
   * for all theories with no conflicts and no lemmas added.
   * If fullModel is true, then we must specify sufficient information for
   * the model class to construct constant representatives for each equivalence
   * class.
   */
  virtual void collectModelInfo( TheoryModel* m, bool fullModel ){ }
  /** if theories want to do something with model after building, do it here */
  virtual void postProcessModel( TheoryModel* m ){ }
  
  /**
   * Return a decision request, if the theory has one, or the NULL node
   * otherwise.
   * If returning non-null node, hould set priority to
   *                        0 if decision is necessary for model-soundness,
   *                        1 if decision is necessary for completeness,
   *                        >1 otherwise.
   */
  virtual Node getNextDecisionRequest( unsigned& priority ) { return Node(); }

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
   * before an input atom to the engine.
   */
  virtual Node ppRewrite(TNode atom) { return atom; }

  /**
   * Don't preprocess subterm of this term
   */
  virtual bool ppDontRewriteSubterm(TNode atom) { return false; }
  
  /** notify preprocessed assertions
   *  Called on new assertions after preprocessing before they are asserted to theory engine.
   *  Should not modify assertions.
  */
  virtual void ppNotifyAssertions( std::vector< Node >& assertions ) {}

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
    Unimplemented("Theory %s doesn't support Theory::setUserAttribute interface",
                  identify().c_str());
  }

  /** A set of theories */
  typedef uint32_t Set;

  /** A set of all theories */
  static const Set AllTheories = (1 << theory::THEORY_LAST) - 1;

  /** Pops a first theory off the set */
  static inline TheoryId setPop(Set& set) {
    uint32_t i = ffs(set); // Find First Set (bit)
    if (i == 0) { return THEORY_LAST; }
    TheoryId id = (TheoryId)(i-1);
    set = setRemove(id, set);
    return id;
  }

  /** Returns the size of a set of theories */
  static inline size_t setSize(Set set) {
    size_t count = 0;
    while (setPop(set) != THEORY_LAST) {
      ++ count;
    }
    return count;
  }

  /** Returns the index size of a set of theories */
  static inline size_t setIndex(TheoryId id, Set set) {
    Assert (setContains(id, set));
    size_t count = 0;
    while (setPop(set) != id) {
      ++ count;
    }
    return count;
  }

  /** Add the theory to the set. If no set specified, just returns a singleton set */
  static inline Set setInsert(TheoryId theory, Set set = 0) {
    return set | (1 << theory);
  }

  /** Add the theory to the set. If no set specified, just returns a singleton set */
  static inline Set setRemove(TheoryId theory, Set set = 0) {
    return setDifference(set, setInsert(theory));
  }

  /** Check if the set contains the theory */
  static inline bool setContains(TheoryId theory, Set set) {
    return set & (1 << theory);
  }

  static inline Set setComplement(Set a) {
    return (~a) & AllTheories;
  }

  static inline Set setIntersection(Set a, Set b) {
    return a & b;
  }

  static inline Set setUnion(Set a, Set b) {
    return a | b;
  }

  /** a - b  */
  static inline Set setDifference(Set a, Set b) {
    return (~b) & a;
  }

  static inline std::string setToString(theory::Theory::Set theorySet) {
    std::stringstream ss;
    ss << "[";
    for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
      if (theory::Theory::setContains((theory::TheoryId)theoryId, theorySet)) {
        ss << (theory::TheoryId) theoryId << " ";
      }
    }
    ss << "]";
    return ss.str();
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
  bool hasFacts() { 
    return !d_facts.empty(); 
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
  std::hash_set<TNode, TNodeHashFunction> currentlySharedTerms() const;

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
   * The search is controlled by the parameter params.  For default behavior,
   * this may be left NULL.
   *
   * Theories that want parameters extend the virtual EntailmentCheckParameters
   * class.  Users ask the theory for an appropriate subclass from the theory
   * and configure that.  How this is implemented is on a per theory basis.
   *
   * The search may provide additional output to guide the user of
   * this function.  This output is stored in a EntailmentCheckSideEffects*
   * output parameter.  The implementation of this is theory specific.  For
   * no output, this is NULL.
   *
   * Theories may not touch their output stream during an entailment check.
   *
   * @param  lit     a literal belonging to the theory.
   * @param  params  the control parameters for the entailment check.
   * @param  out     a theory specific output object of the entailment search.
   * @return         a pair <b,E> s.t. if b is true, then a formula E such that
   * E |= lit in the theory.
   */
  virtual std::pair<bool, Node> entailmentCheck(TNode lit, const EntailmentCheckParameters* params = NULL, EntailmentCheckSideEffects* out = NULL);

  /* equality engine TODO: use? */
  virtual eq::EqualityEngine * getEqualityEngine() { return NULL; }
  
  /* get extended theory */
  virtual ExtTheory * getExtTheory() { return d_extt; }

  /* get current substitution at an effort
   *   input : vars
   *   output : subs, exp 
   *   where ( exp[vars[i]] => vars[i] = subs[i] ) holds for all i
  */
  virtual bool getCurrentSubstitution( int effort, std::vector< Node >& vars, std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp ) { return false; }
  
  /* get reduction for node
       if return value is not 0, then n is reduced. 
       if return value <0 then n is reduced SAT-context-independently (e.g. by a lemma that persists at this user-context level).
       if nr is non-null, then ( n = nr ) should be added as a lemma by caller, and return value should be <0.
   */
  virtual int getReduction( int effort, Node n, Node& nr ) { return 0; }

  /**
   * Turn on proof-production mode.
   */
  void produceProofs() { d_proofsEnabled = true; }

};/* class Theory */

std::ostream& operator<<(std::ostream& os, theory::Theory::Effort level);
inline std::ostream& operator<<(std::ostream& out, const theory::Assertion& a);

inline theory::Assertion Theory::get() {
  Assert( !done(), "Theory::get() called with assertion queue empty!" );

  // Get the assertion
  Assertion fact = d_facts[d_factsHead];
  d_factsHead = d_factsHead + 1;

  Trace("theory") << "Theory::get() => " << fact << " (" << d_facts.size() - d_factsHead << " left)" << std::endl;

  if(Dump.isOn("state")) {
    Dump("state") << AssertCommand(fact.assertion.toExpr());
  }

  return fact;
}

inline std::ostream& operator<<(std::ostream& out, const theory::Assertion& a) {
  return out << a.assertion;
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

class EntailmentCheckParameters {
private:
  TheoryId d_tid;
protected:
  EntailmentCheckParameters(TheoryId tid);
public:
  TheoryId getTheoryId() const;
  virtual ~EntailmentCheckParameters();
};/* class EntailmentCheckParameters */

class EntailmentCheckSideEffects {
private:
  TheoryId d_tid;
protected:
  EntailmentCheckSideEffects(TheoryId tid);
public:
  TheoryId getTheoryId() const;
  virtual ~EntailmentCheckSideEffects();
};/* class EntailmentCheckSideEffects */


class ExtTheory {
  friend class Theory;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
protected:
  Theory * d_parent;
  Node d_true;
  //extended string terms, map to whether they are active
  NodeBoolMap d_ext_func_terms;
  //set of terms from d_ext_func_terms that are SAT-context-independently inactive 
  //  (e.g. term t when a reduction lemma of the form t = t' was added)
  NodeSet d_ci_inactive;
  //cache of all lemmas sent
  NodeSet d_lemmas;
  NodeSet d_pp_lemmas;
  //watched term for checking if any non-reduced extended functions exist 
  context::CDO< Node > d_has_extf;
  //extf kind
  std::map< Kind, bool > d_extf_kind;
  //information for each term in d_ext_func_terms
  class ExtfInfo {
  public:
    //all variables in this term
    std::vector< Node > d_vars;
  };
  std::map< Node, ExtfInfo > d_extf_info;
  //collect variables
  void collectVars( Node n, std::vector< Node >& vars, std::map< Node, bool >& visited );
  // is context dependent inactive
  bool isContextIndependentInactive( Node n );
  //do inferences internal
  bool doInferencesInternal( int effort, std::vector< Node >& terms, std::vector< Node >& nred, bool batch, bool isRed ); 
  //send lemma
  bool sendLemma( Node lem, bool preprocess = false );
  //register term (recursive)
  void registerTermRec( Node n, std::map< Node, bool >& visited );
public:
  ExtTheory( Theory * p );
  virtual ~ExtTheory(){}
  //add extf kind
  void addFunctionKind( Kind k ) { d_extf_kind[k] = true; }
  bool hasFunctionKind( Kind k ) { return d_extf_kind.find( k )!=d_extf_kind.end(); }
  //register term
  //  adds n to d_ext_func_terms if addFunctionKind( n.getKind() ) was called
  void registerTerm( Node n );
  void registerTermRec( Node n );
  // set n as reduced/inactive
  //   if contextDepend = false, then n remains inactive in the duration of this user-context level
  void markReduced( Node n, bool contextDepend = true );
  // mark that a and b are congruent terms: set b inactive, set a to inactive if b was inactive
  void markCongruent( Node a, Node b );
  
  //getSubstitutedTerms
  //  input : effort, terms
  //  output : sterms, exp, where ( exp[i] => terms[i] = sterms[i] ) for all i
  void getSubstitutedTerms( int effort, std::vector< Node >& terms, std::vector< Node >& sterms, std::vector< std::vector< Node > >& exp );
  //doInferences
  //  * input : effort, terms, batch (whether to send one lemma or lemmas for all terms)
  //  *   sends rewriting lemmas of the form ( exp => t = c ) where t is in terms and c is a constant, c = rewrite( t*sigma ) where exp |= sigma
  //  * output : nred (the terms that are still active)
  //  * return : true iff lemma is sent
  bool doInferences( int effort, std::vector< Node >& terms, std::vector< Node >& nred, bool batch=true ); 
  bool doInferences( int effort, std::vector< Node >& nred, bool batch=true  );
  //doReductions 
  //  same as doInferences, but will send reduction lemmas of the form ( t = t' ) where t is in terms, t' is equivalent, reduced term
  bool doReductions( int effort, std::vector< Node >& terms, std::vector< Node >& nred, bool batch=true  ); 
  bool doReductions( int effort, std::vector< Node >& nred, bool batch=true  ); 

  //has active term 
  bool hasActiveTerm();
  //is n active
  bool isActive( Node n );
  //get the set of active terms from d_ext_func_terms
  void getActive( std::vector< Node >& active );
  //get the set of active terms from d_ext_func_terms of kind k
  void getActive( std::vector< Node >& active, Kind k );
};

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_H */
