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
 ** \brief The theory engine.
 **
 ** The theory engine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_ENGINE_H
#define __CVC4__THEORY_ENGINE_H

#include <deque>

#include "expr/node.h"
#include "prop/prop_engine.h"
#include "theory/shared_term_manager.h"
#include "theory/theory.h"
#include "theory/rewriter.h"
#include "theory/valuation.h"
#include "util/options.h"
#include "util/stats.h"

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

  /** A table of from theory ifs to theory pointers */
  theory::Theory* d_theoryTable[theory::THEORY_LAST];

  /**
   * An output channel for Theory that passes messages
   * back to a TheoryEngine.
   */
  class EngineOutputChannel : public theory::OutputChannel {

    friend class TheoryEngine;

    TheoryEngine* d_engine;
    context::Context* d_context;
    context::CDO<Node> d_conflictNode;
    context::CDO<Node> d_explanationNode;

    /**
     * Literals that are propagated by the theory. Note that these are TNodes.
     * The theory can only propagate nodes that have an assigned literal in the
     * sat solver and are hence referenced in the SAT solver.
     */
    std::vector<TNode> d_propagatedLiterals;

    /** Time spent in newFact() (largely spent doing term registration) */
    KEEP_STATISTIC(TimerStat,
                   d_newFactTimer,
                   "theory::newFactTimer");

  public:

    EngineOutputChannel(TheoryEngine* engine, context::Context* context) :
      d_engine(engine),
      d_context(context),
      d_conflictNode(context),
      d_explanationNode(context){
    }

    void newFact(TNode n);

    void conflict(TNode conflictNode, bool safe)
      throw(theory::Interrupted, AssertionException) {
      Debug("theory") << "EngineOutputChannel::conflict("
                      << conflictNode << ")" << std::endl;
      d_conflictNode = conflictNode;
      ++(d_engine->d_statistics.d_statConflicts);
      if(safe) {
        throw theory::Interrupted();
      }
    }

    void propagate(TNode lit, bool)
      throw(theory::Interrupted, AssertionException) {
      d_propagatedLiterals.push_back(lit);
      ++(d_engine->d_statistics.d_statPropagate);
    }

    void lemma(TNode node, bool)
      throw(theory::Interrupted, AssertionException) {
      Debug("theory") << "EngineOutputChannel::lemma("
                      << node << ")" << std::endl;
      ++(d_engine->d_statistics.d_statLemma);
      d_engine->newLemma(node);
    }

    void explanation(TNode explanationNode, bool)
      throw(theory::Interrupted, AssertionException) {
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
   * Replace ITE forms in a node.
   */
  Node removeITEs(TNode t);

public:

  /**
   * Construct a theory engine.
   */
  TheoryEngine(context::Context* ctxt);

  /**
   * Destroy a theory engine.
   */
  ~TheoryEngine();

  /**
   * Adds a theory. Only one theory per theoryId can be present, so if there is another theory it will be deleted.
   */
  template <class TheoryClass>
  void addTheory() {
    TheoryClass* theory = new TheoryClass(d_context, d_theoryOut, theory::Valuation(this));
    d_theoryTable[theory->getId()] = theory;
    d_sharedTermManager->registerTheory(static_cast<TheoryClass*>(theory));
  }

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
    for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++ theoryId) {
      if (d_theoryTable[theoryId]) {
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
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(const TypeNode& typeNode) {
    return d_theoryTable[theory::Theory::theoryOf(typeNode)];
  }

  /**
   * Preprocess a node.  This involves theory-specific rewriting, then
   * calling preRegisterTerm() on what's left over.
   * @param n the node to preprocess
   */
  Node preprocess(TNode n);
  void preRegister(TNode preprocessed);

  /**
   * Assert the formula to the appropriate theory.
   * @param node the assertion
   */
  inline void assertFact(TNode node) {
    Debug("theory") << "TheoryEngine::assertFact(" << node << ")" << std::endl;

    // Mark it as asserted in this context
    //
    // [MGD] removed for now, this appears to have a nontrivial
    // performance penalty
    // node.setAttribute(theory::Asserted(), true);

    // Get the atom
    TNode atom = node.getKind() == kind::NOT ? node[0] : node;

    // Again, eqaulity is a special case
    if (atom.getKind() == kind::EQUAL) {
      theory::TheoryId theoryLHS = theory::Theory::theoryOf(atom[0]);
      Debug("theory") << "asserting " << node << " to " << theoryLHS << std::endl;
      d_theoryTable[theoryLHS]->assertFact(node);
//      theory::TheoryId theoryRHS = theory::Theory::theoryOf(atom[1]);
//      if (theoryLHS != theoryRHS) {
//        Debug("theory") << "asserting " << node << " to " << theoryRHS << std::endl;
//        d_theoryTable[theoryRHS]->assertFact(node);
//      }
//      theory::TheoryId typeTheory = theory::Theory::theoryOf(atom[0].getType());
//      if (typeTheory!= theoryLHS && typeTheory != theoryRHS) {
//        Debug("theory") << "asserting " << node << " to " << typeTheory << std::endl;
//        d_theoryTable[typeTheory]->assertFact(node);
//      }
    } else {
      theory::Theory* theory = theoryOf(atom);
      Debug("theory") << "asserting " << node << " to " << theory->getId() << std::endl;
      theory->assertFact(node);
    }
  }

  /**
   * Check all (currently-active) theories for conflicts.
   * @param effort the effort level to use
   */
  bool check(theory::Theory::Effort effort);

  /**
   * Calls staticLearning() on all active theories, accumulating their
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

  inline void newLemma(TNode node) {
    d_propEngine->assertLemma(preprocess(node));
  }

  /**
   * Returns the last conflict (if any).
   */
  inline Node getConflict() {
    return d_theoryOut.d_conflictNode;
  }

  void propagate();

  inline Node getExplanation(TNode node, theory::Theory* theory) {
    theory->explain(node);
    return d_theoryOut.d_explanationNode;
  }

  inline Node getExplanation(TNode node) {
    d_theoryOut.d_explanationNode = Node::null();
    TNode atom = node.getKind() == kind::NOT ? node[0] : node;
    if (atom.getKind() == kind::EQUAL) {
      theoryOf(atom[0])->explain(node);
    } else {
      theoryOf(atom)->explain(node);
    }
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
      d_statExplanation("theory::explanation", 0)
    {
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
  };
  Statistics d_statistics;

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */
