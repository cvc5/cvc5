/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway, barrett, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory engine
 **
 ** The theory engine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_ENGINE_H
#define __CVC4__THEORY_ENGINE_H

#include <deque>
#include <vector>
#include <utility>

#include "decision/decision_engine.h"
#include "expr/node.h"
#include "expr/command.h"
#include "prop/prop_engine.h"
#include "context/cdhashset.h"
#include "theory/theory.h"
#include "theory/substitutions.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/valuation.h"
#include "util/options.h"
#include "util/stats.h"
#include "util/hash.h"
#include "util/cache.h"
#include "theory/ite_simplifier.h"
#include "theory/unconstrained_simplifier.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

struct NodeTheoryPair {
  Node node;
  theory::TheoryId theory;
  NodeTheoryPair(TNode node, theory::TheoryId theory)
  : node(node), theory(theory) {}
  NodeTheoryPair()
  : theory(theory::THEORY_LAST) {}
  bool operator == (const NodeTheoryPair& pair) const {
    return node == pair.node && theory == pair.theory;
  }
};/* struct NodeTheoryPair */

struct NodeTheoryPairHashFunction {
  NodeHashFunction hashFunction;
  size_t operator()(const NodeTheoryPair& pair) const {
    return hashFunction(pair.node)*0x9e3779b9 + pair.theory;
  }
};/* struct NodeTheoryPairHashFunction */

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {

  /** Associated PropEngine engine */
  prop::PropEngine* d_propEngine;

  /** Access to decision engine */
  DecisionEngine* d_decisionEngine;

  /** Our context */
  context::Context* d_context;

  /** Our user context */
  context::UserContext* d_userContext;

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

  // NotifyClass: template helper class for Shared Terms Database
  class NotifyClass :public SharedTermsDatabase::SharedTermsNotifyClass {
    TheoryEngine& d_theoryEngine;
  public:
    NotifyClass(TheoryEngine& engine): d_theoryEngine(engine) {}
    ~NotifyClass() {}

    void notify(TNode literal, TNode original, theory::TheoryId theory) {
      d_theoryEngine.propagateSharedLiteral(literal, original, theory);
    }
  };

  // Instance of NotifyClass
  NotifyClass d_notify;

  /**
   * The database of shared terms.
   */
  SharedTermsDatabase d_sharedTerms;

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  typedef std::hash_map<TNode, Node, TNodeHashFunction> TNodeMap;

  /**
  * Cache for theory-preprocessing of assertions
   */
  NodeMap d_ppCache;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A set of all
   * theory-propagable literals.
   */
  context::CDList<TNode> d_possiblePropagations;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A
   * context-dependent set of those theory-propagable literals that
   * have been propagated.
   */
  context::CDHashSet<TNode, TNodeHashFunction> d_hasPropagated;

  /**
   * Statistics for a particular theory.
   */
  class Statistics {

    static std::string mkName(std::string prefix,
                              theory::TheoryId theory,
                              std::string suffix) {
      std::stringstream ss;
      ss << prefix << theory << suffix;
      return ss.str();
    }

  public:

    IntStat conflicts, propagations, lemmas, propagationsAsDecisions;

    Statistics(theory::TheoryId theory):
      conflicts(mkName("theory<", theory, ">::conflicts"), 0),
      propagations(mkName("theory<", theory, ">::propagations"), 0),
      lemmas(mkName("theory<", theory, ">::lemmas"), 0),
      propagationsAsDecisions(mkName("theory<", theory, ">::propagationsAsDecisions"), 0)
    {
      StatisticsRegistry::registerStat(&conflicts);
      StatisticsRegistry::registerStat(&propagations);
      StatisticsRegistry::registerStat(&lemmas);
      StatisticsRegistry::registerStat(&propagationsAsDecisions);
    }

    ~Statistics() {
      StatisticsRegistry::unregisterStat(&conflicts);
      StatisticsRegistry::unregisterStat(&propagations);
      StatisticsRegistry::unregisterStat(&lemmas);
      StatisticsRegistry::unregisterStat(&propagationsAsDecisions);
    }
  };/* class TheoryEngine::Statistics */


  /**
   * An output channel for Theory that passes messages
   * back to a TheoryEngine.
   */
  class EngineOutputChannel : public theory::OutputChannel {

    friend class TheoryEngine;

    /**
     * The theory engine we're communicating with.
     */
    TheoryEngine* d_engine;

    /**
     * The statistics of the theory interractions.
     */
    Statistics d_statistics;

    /**
     * The theory owning this chanell.
     */
    theory::TheoryId d_theory;

  public:

    EngineOutputChannel(TheoryEngine* engine, theory::TheoryId theory) :
      d_engine(engine),
      d_statistics(theory),
      d_theory(theory)
    {
    }

    void conflict(TNode conflictNode) throw(AssertionException) {
      Trace("theory::conflict") << "EngineOutputChannel<" << d_theory << ">::conflict(" << conflictNode << ")" << std::endl;
      ++ d_statistics.conflicts;
      d_engine->d_outputChannelUsed = true;
      d_engine->conflict(conflictNode, d_theory);
    }

    void propagate(TNode literal) throw(AssertionException) {
      Trace("theory::propagate") << "EngineOutputChannel<" << d_theory << ">::propagate(" << literal << ")" << std::endl;
      ++ d_statistics.propagations;
      d_engine->d_outputChannelUsed = true;
      d_engine->propagate(literal, d_theory);
    }

    void propagateAsDecision(TNode literal) throw(AssertionException) {
      Trace("theory::propagate") << "EngineOutputChannel<" << d_theory << ">::propagateAsDecision(" << literal << ")" << std::endl;
      ++ d_statistics.propagationsAsDecisions;
      d_engine->d_outputChannelUsed = true;
      d_engine->propagateAsDecision(literal, d_theory);
    }

    theory::LemmaStatus lemma(TNode lemma, bool removable = false) throw(TypeCheckingExceptionPrivate, AssertionException) {
      Trace("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma(" << lemma << ")" << std::endl;
      ++ d_statistics.lemmas;
      d_engine->d_outputChannelUsed = true;
      return d_engine->lemma(lemma, false, removable);
    }

    void setIncomplete() throw(AssertionException) {
      d_engine->setIncomplete(d_theory);
    }

    void spendResource() throw() {
      d_engine->spendResource();
    }

  };/* class TheoryEngine::EngineOutputChannel */

  /**
   * Output channels for individual theories.
   */
  EngineOutputChannel* d_theoryOut[theory::THEORY_LAST];

  /**
   * Are we in conflict.
   */
  context::CDO<bool> d_inConflict;

  /**
   * Explain the equality literals and push all the explaining literals
   * into the builder. All the non-equality literals are pushed to the
   * builder.
   */
  void explainEqualities(theory::TheoryId theoryId, TNode literals, NodeBuilder<>& builder);

  /**
   * Same as above, but just for single equalities.
   */
  void explainEquality(theory::TheoryId theoryId, TNode eqLiteral, NodeBuilder<>& builder);

  /**
   * Called by the theories to notify of a conflict.
   */
  void conflict(TNode conflict, theory::TheoryId theoryId);

  /**
   * Called by shared terms database to notify of a conflict.
   */
  void sharedConflict(TNode conflict);

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

  /**
   * Called by the theories to notify that the current branch is incomplete.
   */
  void setIncomplete(theory::TheoryId theory) {
    d_incomplete = true;
  }

  /**
   * "Spend" a resource during a search or preprocessing.
   */
  void spendResource() throw() {
    d_propEngine->spendResource();
  }

  struct SharedLiteral {
    /**
     * The node/theory pair for the assertion. THEORY_LAST indicates this is a SAT
     * literal and should be sent to the SAT solver
     */
    NodeTheoryPair toAssert;
    /** This is the node that we will use to explain it */
    Node toExplain;

    SharedLiteral(TNode assertion, TNode original, theory::TheoryId receivingTheory)
    : toAssert(assertion, receivingTheory),
      toExplain(original)
    { }
  };

  /**
   * Map from nodes to theories.
   */
  typedef context::CDHashMap<Node, theory::TheoryId, NodeHashFunction> SharedLiteralsInMap;

  /**
   * All shared literals asserted to theory engine.
   * Maps from literal to the theory that sent the literal (THEORY_LAST means sent from SAT).
   */
  SharedLiteralsInMap d_sharedLiteralsIn;

  /**
   * Map from literals asserted by theory engine to literal that can explain
   */
  typedef context::CDHashMap<NodeTheoryPair, Node, NodeTheoryPairHashFunction> AssertedLiteralsOutMap;

  /**
   * All literals asserted to theories from theory engine.
   * Maps from literal/theory pair to literal that can explain this assertion.
   */
  AssertedLiteralsOutMap d_assertedLiteralsOut;

  /**
   * Shared literals queud up to be asserted to the individual theories.
   */
  std::vector<SharedLiteral> d_propagatedSharedLiterals;

  void propagateSharedLiteral(TNode literal, TNode original, theory::TheoryId theory)
  {
    if (literal.getKind() == kind::CONST_BOOLEAN) {
      Assert(!literal.getConst<bool>());
      sharedConflict(original);
    }
    else {
      d_propagatedSharedLiterals.push_back(SharedLiteral(literal, original, theory));
    }
  }

  /**
   * Assert the shared literals that are queued up to the theories.
   */
  void outputSharedLiterals();

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
   * Decisions that are requested via propagateAsDecision().  The theory
   * can only request decisions on nodes that have an assigned litearl in
   * the SAT solver and are hence referenced in the SAT solver (making the
   * use of TNode safe).
   */
  context::CDList<TNode> d_decisionRequests;

  /**
   * The index of the next decision requested by a theory.
   */
  context::CDO<unsigned> d_decisionRequestsIndex;

  /**
   * Called by the output channel to propagate literals and facts
   */
  void propagate(TNode literal, theory::TheoryId theory);

  /**
   * Internal method to call the propagation routines and collect the
   * propagated literals.
   */
  void propagate(theory::Theory::Effort effort);

  /**
   * Called by the output channel to request decisions "as soon as
   * possible."
   */
  void propagateAsDecision(TNode literal, theory::TheoryId theory);

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

  /**
   * Adds a new lemma, returning its status.
   */
  theory::LemmaStatus lemma(TNode node, bool negated, bool removable) {
    if(Dump.isOn("t-lemmas")) {
      Dump("t-lemmas") << CommentCommand("theory lemma: expect valid")
                       << QueryCommand(node.toExpr());
    }

    // Share with other portfolio threads
    if(Options::current()->lemmaOutputChannel != NULL) {
      Options::current()->lemmaOutputChannel->notifyNewLemma(node.toExpr());
    }

    // Remove the ITEs
    std::vector<Node> additionalLemmas;
    IteSkolemMap iteSkolemMap;
    additionalLemmas.push_back(node);
    RemoveITE::run(additionalLemmas, iteSkolemMap);
    additionalLemmas[0] = theory::Rewriter::rewrite(additionalLemmas[0]);

    // assert to prop engine
    d_propEngine->assertLemma(additionalLemmas[0], negated, removable);
    for (unsigned i = 1; i < additionalLemmas.size(); ++ i) {
      additionalLemmas[i] = theory::Rewriter::rewrite(additionalLemmas[i]);
      d_propEngine->assertLemma(additionalLemmas[i], false, removable);
    }

    // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.
    // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.
    if(negated) {
      // Can't we just get rid of passing around this 'negated' stuff?
      // Is it that hard for the propEngine to figure that out itself?
      // (I like the use of triple negation <evil laugh>.) --K
      additionalLemmas[0] = additionalLemmas[0].notNode();
      negated = false;
    }
    // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.
    // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.

    // assert to decision engine
    if(!removable)
      d_decisionEngine->addAssertions(additionalLemmas, 1, iteSkolemMap);

    // Mark that we added some lemmas
    d_lemmasAdded = true;

    // Lemma analysis isn't online yet; this lemma may only live for this
    // user level.
    return theory::LemmaStatus(additionalLemmas[0], d_userContext->getLevel());
  }

  /** Time spent in theory combination */
  TimerStat d_combineTheoriesTime;

  Node d_true;
  Node d_false;

public:

  /** Constructs a theory engine */
  TheoryEngine(context::Context* context, context::UserContext* userContext, const LogicInfo& logic);

  /** Destroys a theory engine */
  ~TheoryEngine();

  /**
   * Adds a theory. Only one theory per TheoryId can be present, so if
   * there is another theory it will be deleted.
   */
  template <class TheoryClass>
  inline void addTheory(theory::TheoryId theoryId) {
    Assert(d_theoryTable[theoryId] == NULL && d_theoryOut[theoryId] == NULL);
    d_theoryOut[theoryId] = new EngineOutputChannel(this, theoryId);
    d_theoryTable[theoryId] = new TheoryClass(d_context, d_userContext, *d_theoryOut[theoryId], theory::Valuation(this), d_logicInfo);
  }

  inline void setPropEngine(prop::PropEngine* propEngine) {
    Assert(d_propEngine == NULL);
    d_propEngine = propEngine;
  }

  inline void setDecisionEngine(DecisionEngine* decisionEngine) {
    Assert(d_decisionEngine == NULL);
    d_decisionEngine = decisionEngine;
  }

  /**
   * Get a pointer to the underlying propositional engine.
   */
  inline prop::PropEngine* getPropEngine() const {
    return d_propEngine;
  }

private:

  /**
   * Helper for preprocess
   */
  Node ppTheoryRewrite(TNode term);

  /**
   * Queue of nodes for pre-registration.
   */
  std::queue<TNode> d_preregisterQueue;

  /**
   * Boolean flag denoting we are in pre-registration.
   */
  bool d_inPreregister;

public:

  /**
   * Signal the start of a new round of assertion preprocessing
   */
  void preprocessStart();

  /**
   * Runs theory specific preprocesssing on the non-Boolean parts of
   * the formula.  This is only called on input assertions, after ITEs
   * have been removed.
   */
  Node preprocess(TNode node);

  /**
   * Return whether or not we are incomplete (in the current context).
   */
  inline bool isIncomplete() const {
    return d_incomplete;
  }

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
   * This is called at shutdown time by the SmtEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory.
   */
  void shutdown();

  /**
   * Solve the given literal with a theory that owns it.
   */
  theory::Theory::PPAssertStatus solve(TNode literal,
                                    theory::SubstitutionMap& substitutionOut);

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
   * Run the combination framework.
   */
  void combineTheories();

  /**
   * Calls ppStaticLearn() on all theories, accumulating their
   * combined contributions in the "learned" builder.
   */
  void ppStaticLearn(TNode in, NodeBuilder<>& learned);

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

  TNode getNextDecisionRequest() {
    if(d_decisionRequestsIndex < d_decisionRequests.size()) {
      TNode req = d_decisionRequests[d_decisionRequestsIndex];
      Debug("propagateAsDecision") << "TheoryEngine requesting decision["
                                   << d_decisionRequestsIndex << "]: "
                                   << req << std::endl;
      d_decisionRequestsIndex = d_decisionRequestsIndex + 1;
      return req;
    } else {
      return TNode::null();
    }
  }

  bool properConflict(TNode conflict) const;
  bool properPropagation(TNode lit) const;
  bool properExplanation(TNode node, TNode expl) const;

  enum ExplainTaskKind {
    // Literal sent out from the theory engine
    SHARED_LITERAL_OUT,
    // Explanation produced by a theory
    THEORY_EXPLANATION,
    // Explanation produced by the shared terms database
    SHARED_DATABASE_EXPLANATION
  };

  struct ExplainTask {
    Node node;
    ExplainTaskKind kind;
    theory::TheoryId theory;
    ExplainTask(Node n, ExplainTaskKind k, theory::TheoryId tid = theory::THEORY_LAST) :
      node(n), kind(k), theory(tid) {}
    bool operator == (const ExplainTask& other) const {
      return node == other.node && kind == other.kind && theory == other.theory;
    }
  };

  struct ExplainTaskHashFunction {
    size_t operator () (const ExplainTask& task) const {
      size_t hash = 0;
      hash = 0x9e3779b9 + NodeHashFunction().operator()(task.node);
      hash ^= 0x9e3779b9 + task.kind + (hash << 6) + (hash >> 2);
      hash ^= 0x9e3779b9 + task.theory + (hash << 6) + (hash >> 2);
      return hash;
    }
  };

  Node getExplanation(TNode node);

  Node explain(ExplainTask toExplain);

  Node getValue(TNode node);

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(TNode node) {
    return d_theoryTable[theory::Theory::theoryOf(node)];
  }

  /**
   * Get the theory associated to a the given theory id. It will also mark the
   * theory as currently active, we assume that theories are called only through
   * theoryOf.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(theory::TheoryId theoryId) {
    return d_theoryTable[theoryId];
  }

  /**
   * Returns the equality status of the two terms, from the theory
   * that owns the domain type.  The types of a and b must be the same.
   */
  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);

private:

  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;

  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;

  /** Prints the assertions to the debug stream */
  void printAssertions(const char* tag);

  /** For preprocessing pass simplifying ITEs */
  ITESimplifier d_iteSimplifier;

  /** For preprocessing pass simplifying unconstrained expressions */
  UnconstrainedSimplifier d_unconstrainedSimp;

public:
  Node ppSimpITE(TNode assertion);
  void ppUnconstrainedSimp(std::vector<Node>& assertions);

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */
