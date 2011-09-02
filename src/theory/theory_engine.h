/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, dejan
 ** Minor contributors (to current version): cconway, barrett
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
#include "prop/prop_engine.h"
#include "theory/shared_term_manager.h"
#include "theory/theory.h"
#include "theory/substitutions.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/valuation.h"
#include "util/options.h"
#include "util/stats.h"
#include "util/hash.h"
#include "util/cache.h"
#include "util/ite_removal.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// PropEngine.

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

  /** A table of from theory IDs to theory pointers */
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
   * Cache from proprocessing of atoms.
   */
  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_atomPreprocessingCache;

  /**
   * An output channel for Theory that passes messages
   * back to a TheoryEngine.
   */
  class EngineOutputChannel : public theory::OutputChannel {

    friend class TheoryEngine;

    TheoryEngine* d_engine;
    context::Context* d_context;
    context::CDO<bool> d_inConflict;
    context::CDO<Node> d_explanationNode;

    /**
     * Literals that are propagated by the theory. Note that these are TNodes.
     * The theory can only propagate nodes that have an assigned literal in the
     * sat solver and are hence referenced in the SAT solver.
     */
    std::vector<TNode> d_propagatedLiterals;

    /**
     * Check if the node is in conflict for debug purposes
     */
    bool isProperConflict(TNode conflictNode) {
      bool value;
      if (conflictNode.getKind() == kind::AND) {
        for (unsigned i = 0; i < conflictNode.getNumChildren(); ++ i) {
          if (!d_engine->getPropEngine()->hasValue(conflictNode[i], value)) return false;
          if (!value) return false;
        }
      } else {
        if (!d_engine->getPropEngine()->hasValue(conflictNode, value)) return false;
        return value;
      }
      return true;
    }

  public:

    EngineOutputChannel(TheoryEngine* engine, context::Context* context) :
      d_engine(engine),
      d_context(context),
      d_inConflict(context, false),
      d_explanationNode(context) {
    }

    void newFact(TNode n);

    void conflict(TNode conflictNode, bool safe)
      throw(theory::Interrupted, AssertionException) {
      Trace("theory") << "EngineOutputChannel::conflict(" << conflictNode << ")" << std::endl;
      d_inConflict = true;

      ++(d_engine->d_statistics.d_statConflicts);

      // Construct the lemma (note that no CNF caching should happen as all the literals already exists)
      Assert(isProperConflict(conflictNode));
      d_engine->newLemma(conflictNode, true, false);

      if(safe) {
        throw theory::Interrupted();
      }
    }

    void propagate(TNode lit, bool)
      throw(theory::Interrupted, AssertionException) {
      Trace("theory") << "EngineOutputChannel::propagate("
                      << lit << ")" << std::endl;
      d_propagatedLiterals.push_back(lit);
      ++(d_engine->d_statistics.d_statPropagate);
    }

    void lemma(TNode node, bool removable = false)
      throw(theory::Interrupted, TypeCheckingExceptionPrivate, AssertionException) {
      Trace("theory") << "EngineOutputChannel::lemma("
                      << node << ")" << std::endl;
      ++(d_engine->d_statistics.d_statLemma);

      d_engine->newLemma(node, false, removable);
    }

    void explanation(TNode explanationNode, bool)
      throw(theory::Interrupted, AssertionException) {
      Trace("theory") << "EngineOutputChannel::explanation("
                      << explanationNode << ")" << std::endl;
      d_explanationNode = explanationNode;
      ++(d_engine->d_statistics.d_statExplanation);
    }

    void setIncomplete()
      throw(theory::Interrupted, AssertionException) {
      d_engine->d_incomplete = true;
    }
  };/* class EngineOutputChannel */

  EngineOutputChannel d_theoryOut;

  /** Pointer to Shared Term Manager */
  SharedTermManager* d_sharedTermManager;

  /**
   * Whether or not theory registration is on.  May not be safe to
   * turn off with some theories.
   */
  bool d_theoryRegistration;

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
   * Mark a theory active if it's not already.
   */
  void markActive(theory::Theory::Set theories) {
    d_activeTheories = theory::Theory::setUnion(d_activeTheories, theories);
  }

  /**
   * Is the theory active.
   */
  bool isActive(theory::TheoryId theory) {
    return theory::Theory::setContains(theory, d_activeTheories);
  }

  /** The logic of the problem */
  std::string d_logic;

public:

  /** Constructs a theory engine */
  TheoryEngine(context::Context* ctxt);

  /** Destroys a theory engine */
  ~TheoryEngine();

  /**
   * Adds a theory. Only one theory per TheoryId can be present, so if
   * there is another theory it will be deleted.
   */
  template <class TheoryClass>
  void addTheory() {
    TheoryClass* theory = new TheoryClass(d_context, d_theoryOut, theory::Valuation(this));
    d_theoryTable[theory->getId()] = theory;
    d_sharedTermManager->registerTheory(static_cast<TheoryClass*>(theory));
  }

  /**
   * Set's the logic (smt-lib format). All theory specific setup/hacks should go in here.
   */
  void setLogic(std::string logic);

  SharedTermManager* getSharedTermManager() {
    return d_sharedTermManager;
  }

  void setPropEngine(prop::PropEngine* propEngine) {
    Assert(d_propEngine == NULL);
    d_propEngine = propEngine;
  }

  /**
   * Get a pointer to the underlying propositional engine.
   */
  prop::PropEngine* getPropEngine() const {
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
  bool isIncomplete() {
    return d_incomplete;
  }

  /**
   * This is called at shutdown time by the SmtEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory.
   */
  void shutdown() {
    // Set this first; if a Theory shutdown() throws an exception,
    // at least the destruction of the TheoryEngine won't confound
    // matters.
    d_hasShutDown = true;

    // Shutdown all the theories
    for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
      if(d_theoryTable[theoryId]) {
        d_theoryTable[theoryId]->shutdown();
      }
    }

    theory::Rewriter::shutdown();
  }

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
   * Get the theory associated to a the given theory id.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(theory::TheoryId theoryId) {
    return d_theoryTable[theoryId];
  }

  /**
   * Solve the given literal with a theory that owns it.
   */
  theory::Theory::SolveStatus solve(TNode literal, theory::SubstitutionMap& substitionOut);

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
  inline void assertFact(TNode node) {
    Trace("theory") << "TheoryEngine::assertFact(" << node << ")" << std::endl;

    // Get the atom
    TNode atom = node.getKind() == kind::NOT ? node[0] : node;

    theory::Theory* theory = theoryOf(atom);
    Trace("theory") << "asserting " << node << " to " << theory->getId() << std::endl;
    theory->assertFact(node);
  }

  /**
   * Check all (currently-active) theories for conflicts.
   * @param effort the effort level to use
   */
  void check(theory::Theory::Effort effort);

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

  inline const std::vector<TNode>& getPropagatedLiterals() const {
    return d_theoryOut.d_propagatedLiterals;
  }

  void clearPropagatedLiterals() {
    d_theoryOut.d_propagatedLiterals.clear();
  }

  inline void newLemma(TNode node, bool negated, bool removable) {
    // Remove the ITEs and assert to prop engine
    std::vector<Node> additionalLemmas;
    additionalLemmas.push_back(node);
    RemoveITE::run(additionalLemmas);
    d_propEngine->assertLemma(theory::Rewriter::rewrite(additionalLemmas[0]), negated, removable);
    for (unsigned i = 1; i < additionalLemmas.size(); ++ i) {
      d_propEngine->assertLemma(theory::Rewriter::rewrite(additionalLemmas[i]), false, removable);
    }
  }

  void propagate();

  inline Node getExplanation(TNode node, theory::Theory* theory) {
    theory->explain(node);
    return d_theoryOut.d_explanationNode;
  }

  inline Node getExplanation(TNode node) {
    d_theoryOut.d_explanationNode = Node::null();
    TNode atom = node.getKind() == kind::NOT ? node[0] : node;
    theoryOf(atom)->explain(node);
    Assert(!d_theoryOut.d_explanationNode.get().isNull());
    return d_theoryOut.d_explanationNode;
  }

  Node getValue(TNode node);

private:
  class Statistics {
  public:
    IntStat d_statConflicts, d_statPropagate, d_statLemma, d_statAugLemma, d_statExplanation;
    Statistics():
      d_statConflicts("theory::conflicts", 0),
      d_statPropagate("theory::propagate", 0),
      d_statLemma("theory::lemma", 0),
      d_statAugLemma("theory::aug_lemma", 0),
      d_statExplanation("theory::explanation", 0) {
      StatisticsRegistry::registerStat(&d_statConflicts);
      StatisticsRegistry::registerStat(&d_statPropagate);
      StatisticsRegistry::registerStat(&d_statLemma);
      StatisticsRegistry::registerStat(&d_statAugLemma);
      StatisticsRegistry::registerStat(&d_statExplanation);
    }

    ~Statistics() {
      StatisticsRegistry::unregisterStat(&d_statConflicts);
      StatisticsRegistry::unregisterStat(&d_statPropagate);
      StatisticsRegistry::unregisterStat(&d_statLemma);
      StatisticsRegistry::unregisterStat(&d_statAugLemma);
      StatisticsRegistry::unregisterStat(&d_statExplanation);
    }
  };/* class TheoryEngine::Statistics */
  Statistics d_statistics;

  ///////////////////////////
  // Visitors
  ///////////////////////////

  /**
   * Visitor that calls the apropriate theory to preregister the term.
   */
  class PreRegisterVisitor {

    /** The engine */
    TheoryEngine& d_engine;

    /**
     * Cache from proprocessing of atoms.
     */
    typedef context::CDMap<TNode, theory::Theory::Set, TNodeHashFunction> TNodeVisitedMap;
    TNodeVisitedMap d_visited;

    /**
     * All the theories of the visitation.
     */
    theory::Theory::Set d_theories;

    std::string toString() const {
      std::stringstream ss;
      TNodeVisitedMap::const_iterator it = d_visited.begin();
      for (; it != d_visited.end(); ++ it) {
        ss << (*it).first << ": " << theory::Theory::setToString((*it).second) << std::endl;
      }
      return ss.str();
    }

  public:

    PreRegisterVisitor(TheoryEngine& engine, context::Context* context): d_engine(engine), d_visited(context), d_theories(0){}

    bool alreadyVisited(TNode current, TNode parent) {

      Debug("register::internal") << "PreRegisterVisitor::alreadyVisited(" << current << "," << parent << ") => ";

      using namespace theory;

      TNodeVisitedMap::iterator find = d_visited.find(current);

      // If node is not visited at all, just return false
      if (find == d_visited.end()) {
        Debug("register::internal") << "1:false" << std::endl;
        return false;
      }

      Theory::Set theories = (*find).second;

      TheoryId currentTheoryId = Theory::theoryOf(current);
      TheoryId parentTheoryId  = Theory::theoryOf(parent);

      if (Theory::setContains(currentTheoryId, theories)) {
        // The current theory has already visited it, so now it depends on the parent
        Debug("register::internal") << (Theory::setContains(parentTheoryId, theories) ? "2:true" : "2:false") << std::endl;
        return Theory::setContains(parentTheoryId, theories);
      } else {
        // If the current theory is not registered, it still needs to be visited
        Debug("register::internal") << "2:false" << std::endl;
        return false;
      }
    }

    void visit(TNode current, TNode parent) {

      Debug("register") << "PreRegisterVisitor::visit(" << current << "," << parent << ")" << std::endl;
      Debug("register::internal") << toString() << std::endl;

      using namespace theory;

      // Get the theories of the terms
      TheoryId currentTheoryId = Theory::theoryOf(current);
      TheoryId parentTheoryId  = Theory::theoryOf(parent);

      Theory::Set theories = d_visited[current];
      Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): previously registered with " << Theory::setToString(theories) << std::endl;
      if (!Theory::setContains(currentTheoryId, theories)) {
        d_visited[current] = theories = Theory::setInsert(currentTheoryId, theories);
        d_engine.theoryOf(currentTheoryId)->preRegisterTerm(current);
        d_theories = Theory::setInsert(currentTheoryId, d_theories);
        Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): adding " << currentTheoryId << std::endl;
      }
      if (!Theory::setContains(parentTheoryId, theories)) {
        d_visited[current] = theories = Theory::setInsert(parentTheoryId, theories);
        d_engine.theoryOf(parentTheoryId)->preRegisterTerm(current);
        d_theories = Theory::setInsert(parentTheoryId, d_theories);
        Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): adding " << parentTheoryId << std::endl;
      }
      Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): now registered with " << Theory::setToString(theories) << std::endl;

      Assert(d_visited.find(current) != d_visited.end());
      Assert(alreadyVisited(current, parent));
    }

    void start(TNode node) {
      d_theories = 0;
    }

    void done(TNode node) {
      d_engine.markActive(d_theories);
    }

  };

  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */
