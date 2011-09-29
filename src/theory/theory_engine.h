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

#include "expr/node.h"
#include "expr/command.h"
#include "prop/prop_engine.h"
#include "context/cdset.h"
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
#include "util/ite_removal.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

struct NodeTheoryPair {
  Node node;
  theory::TheoryId theory;
  NodeTheoryPair(Node node, theory::TheoryId theory)
  : node(node), theory(theory) {}
  NodeTheoryPair()
  : theory(theory::THEORY_LAST) {}
  bool operator == (const NodeTheoryPair& pair) const {
    return node == pair.node && theory == pair.theory;
  }
};

struct NodeTheoryPairHashFunction {
  NodeHashFunction hashFunction;
  size_t operator()(const NodeTheoryPair& pair) const {
    return hashFunction(pair.node)*0x9e3779b9 + pair.theory;
  }
};

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {

  /** Associated PropEngine engine */
  prop::PropEngine* d_propEngine;

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
   * A bitmap of theories that are "active" for the current run.  We
   * mark a theory active when we firt see a term or type belonging to
   * it.  This is important because we can optimize for single-theory
   * runs (no sharing), can reduce the cost of walking the DAG on
   * registration, etc.
   */
  theory::Theory::Set d_activeTheories;

  /**
   * The database of shared terms.
   */
  SharedTermsDatabase d_sharedTerms;

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;

  /**
   * Cache from proprocessing of atoms.
   */
  NodeMap d_atomPreprocessingCache;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A set of all
   * theory-propagable literals.
   */
  std::vector<TNode> d_possiblePropagations;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A
   * context-dependent set of those theory-propagable literals that
   * have been propagated.
   */
  context::CDSet<TNode, TNodeHashFunction> d_hasPropagated;

  /**
   * Statistics for a particular theory.
   */
  class Statistics {

    static std::string mkName(std::string prefix, theory::TheoryId theory, std::string suffix) {
      std::stringstream ss;
      ss << prefix << theory << suffix;
      return ss.str();
    }

  public:

    IntStat conflicts, propagations, lemmas;

    Statistics(theory::TheoryId theory):
      conflicts(mkName("theory<", theory, ">::conflicts"), 0),
      propagations(mkName("theory<", theory, ">::propagations"), 0),
      lemmas(mkName("theory<", theory, ">::lemmas"), 0)
    {
      StatisticsRegistry::registerStat(&conflicts);
      StatisticsRegistry::registerStat(&propagations);
      StatisticsRegistry::registerStat(&lemmas);
    }

    ~Statistics() {
      StatisticsRegistry::unregisterStat(&conflicts);
      StatisticsRegistry::unregisterStat(&propagations);
      StatisticsRegistry::unregisterStat(&lemmas);
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
      Trace("theory") << "EngineOutputChannel<" << d_theory << ">::conflict(" << conflictNode << ")" << std::endl;
      ++ d_statistics.conflicts;
      d_engine->conflict(conflictNode);
    }

    void propagate(TNode literal) throw(AssertionException) {
      Trace("theory") << "EngineOutputChannel<" << d_theory << ">::propagate(" << literal << ")" << std::endl;
      ++ d_statistics.propagations;
      d_engine->propagate(literal, d_theory);
    }

    void lemma(TNode lemma, bool removable = false) throw(TypeCheckingExceptionPrivate, AssertionException) {
      Trace("theory") << "EngineOutputChannel<" << d_theory << ">::lemma(" << lemma << ")" << std::endl;
      ++ d_statistics.lemmas;
      d_engine->lemma(lemma, false, removable);
    }

    void setIncomplete() throw(AssertionException) {
      d_engine->setIncomplete(d_theory);
    }
  };/* class EngineOutputChannel */

  /**
   * Output channels for individual theories.
   */
  EngineOutputChannel* d_theoryOut[theory::THEORY_LAST];

  /**
   * Are we in conflict.
   */
  context::CDO<bool> d_inConflict;

  void conflict(TNode conflict) {

    Assert(properConflict(conflict));

    // Mark that we are in conflict
    d_inConflict = true;

    if(Dump.isOn("t-conflicts")) {
      Dump("t-conflicts") << CommentCommand("theory conflict: expect unsat") << std::endl
                          << CheckSatCommand(conflict.toExpr()) << std::endl;
    }

    // Construct the lemma (note that no CNF caching should happen as all the literals already exists)
    lemma(conflict, true, false);
  }

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
   * Is the theory active.
   */
  bool isActive(theory::TheoryId theory) {
    return theory::Theory::setContains(theory, d_activeTheories);
  }

  struct SharedEquality {
    /** The node/theory pair for the assertion */
    NodeTheoryPair toAssert;
    /** This is the node/theory pair that we will use to explain it */
    NodeTheoryPair toExplain;
    
    SharedEquality(TNode assertion, TNode original, theory::TheoryId sendingTheory, theory::TheoryId receivingTheory)
    : toAssert(assertion, sendingTheory),
      toExplain(original, receivingTheory)
    { }
  };
  
  /**
   * A map from asserted facts to where they came from (for explanations).
   */
  context::CDMap<NodeTheoryPair, NodeTheoryPair, NodeTheoryPairHashFunction> d_sharedAssertions;

  /**
   * Assert a shared equalities propagated by theories.
   */
  void assertSharedEqualities();

  /** The logic of the problem */
  std::string d_logic;

  /**
   * Literals that are propagated by the theory. Note that these are TNodes.
   * The theory can only propagate nodes that have an assigned literal in the
   * sat solver and are hence referenced in the SAT solver.
   */
  context::CDList<TNode> d_propagatedLiterals;

  /**
   * The index of the next literal to be propagated by a theory.
   */
  context::CDO<unsigned> d_propagatedLiteralsIndex;

  /**
   * Shared term equalities that should be asserted to the individual theories.
   */
  std::vector<SharedEquality> d_propagatedEqualities;

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
   * A variable to mark if we added any lemmas.
   */
  bool d_lemmasAdded;

  /**
   * Adds a new lemma
   */
  void lemma(TNode node, bool negated, bool removable) {

    if(Dump.isOn("t-lemmas")) {
      Dump("t-lemmas") << CommentCommand("theory lemma: expect valid") << std::endl
                       << QueryCommand(node.toExpr()) << std::endl;
    }
    // Remove the ITEs and assert to prop engine
    std::vector<Node> additionalLemmas;
    additionalLemmas.push_back(node);
    RemoveITE::run(additionalLemmas);
    d_propEngine->assertLemma(theory::Rewriter::rewrite(additionalLemmas[0]), negated, removable);
    for (unsigned i = 1; i < additionalLemmas.size(); ++ i) {
      d_propEngine->assertLemma(theory::Rewriter::rewrite(additionalLemmas[i]), false, removable);
    }

    // Mark that we added some lemmas
    d_lemmasAdded = true;
  }

public:

  /** Constructs a theory engine */
  TheoryEngine(context::Context* context, context::UserContext* userContext);

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
    d_theoryTable[theoryId] = new TheoryClass(d_context, d_userContext, *d_theoryOut[theoryId], theory::Valuation(this));
  }

  /**
   * Sets the logic (SMT-LIB format).  All theory specific setup/hacks
   * should go in here.
   */
  void setLogic(std::string logic);

  /**
   * Mark a theory active if it's not already.
   */
  void markActive(theory::Theory::Set theories) {
    d_activeTheories = theory::Theory::setUnion(d_activeTheories, theories);
  }

  inline void setPropEngine(prop::PropEngine* propEngine) {
    Assert(d_propEngine == NULL);
    d_propEngine = propEngine;
  }

  /**
   * Get a pointer to the underlying propositional engine.
   */
  inline prop::PropEngine* getPropEngine() const {
    return d_propEngine;
  }

  /**
   * Runs theory specific preprocesssing on the non-Boolean parts of the formula.
   * This is only called on input assertions, after ITEs have been removed.
   */
  Node preprocess(TNode node);

  /**
   * Return whether or not we are incomplete (in the current context).
   */
  inline bool isIncomplete() {
    return d_incomplete;
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
  theory::Theory::SolveStatus solve(TNode literal,
                                    theory::SubstitutionMap& substitutionOut);

  /**
   * Preregister a Theory atom with the responsible theory (or
   * theories).
   */
  void preRegister(TNode preprocessed);

  /**
   * Call the theories to perform one last rewrite on the theory atoms
   * if they wish. This last rewrite is only performed on the input atoms.
   * At this point it is ensured that atoms do not contain any Boolean
   * strucure, i.e. there is no ITE nodes in them.
   *
   */
  Node preCheckRewrite(TNode node);

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
   * Calls staticLearning() on all theories, accumulating their
   * combined contributions in the "learned" builder.
   */
  void staticLearning(TNode in, NodeBuilder<>& learned);

  /**
   * Calls presolve() on all active theories and returns true
   * if one of the theories discovers a conflict.
   */
  bool presolve();

  /**
   * Calls notifyRestart() on all active theories.
   */
  void notifyRestart();

  void getPropagatedLiterals(std::vector<TNode>& literals) {
    for (; d_propagatedLiteralsIndex < d_propagatedLiterals.size(); d_propagatedLiteralsIndex = d_propagatedLiteralsIndex + 1) {
      literals.push_back(d_propagatedLiterals[d_propagatedLiteralsIndex]);
    }
  }

  Node getExplanation(TNode node, theory::Theory* theory);

  bool properConflict(TNode conflict) const;
  bool properPropagation(TNode lit) const;
  bool properExplanation(TNode node, TNode expl) const;

  inline Node getExplanation(TNode node) {
    TNode atom = node.getKind() == kind::NOT ? node[0] : node;
    Node explanation = theoryOf(atom)->explain(node);
    Assert(!explanation.isNull());
    if(Dump.isOn("t-explanations")) {
      Dump("t-explanations") << CommentCommand(std::string("theory explanation from ") + theoryOf(atom)->identify() + ": expect valid") << std::endl
        << QueryCommand(explanation.impNode(node).toExpr()) << std::endl;
    }
    Assert(properExplanation(node, explanation));
    return explanation;
  }

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

private:

  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;

  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor; 

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */
