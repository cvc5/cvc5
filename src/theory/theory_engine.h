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
  bool d_theoryIsActive[theory::THEORY_LAST];

  /**
   * The count of active theories in the d_theoryIsActive bitmap.
   */
  size_t d_activeTheories;

  /**
   * Need the registration infrastructure when theory sharing is on
   * (>=2 active theories) or when the sole active theory has
   * requested it.
   */
  bool d_needRegistration;

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

    /** Time spent in newFact() (largely spent doing term registration) */
    KEEP_STATISTIC(TimerStat,
                   d_newFactTimer,
                   "theory::newFactTimer");

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
      d_engine->newLemma(conflictNode, true, true);

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
      throw(theory::Interrupted, AssertionException) {
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
  void markActive(theory::TheoryId th) {
    if(!d_theoryIsActive[th]) {
      d_theoryIsActive[th] = true;
      if(th != theory::THEORY_BUILTIN && th != theory::THEORY_BOOL) {
        if(++d_activeTheories == 1) {
          // theory requests registration
          d_needRegistration = hasRegisterTerm(th);
        } else {
          // need it for sharing
          d_needRegistration = true;
        }
      }
      Notice() << "Theory " << th << " has been activated (registration is "
               << (d_needRegistration ? "on" : "off") << ")." << std::endl;
    }
  }

  bool hasRegisterTerm(theory::TheoryId th) const;

public:
  /** The logic of the problem */
  std::string d_logic;

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
    TheoryClass* theory =
      new TheoryClass(d_context, d_theoryOut, theory::Valuation(this));
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
    if (node.getKind() == kind::EQUAL) {
      return d_theoryTable[theoryIdOf(node[0])];
    } else {
      return d_theoryTable[theoryIdOf(node)];
    }
  }

  /**
   * Wrapper for theory::Theory::theoryOf() that implements the
   * array/EUF hack.
   */
  inline theory::TheoryId theoryIdOf(TNode node) {
    theory::TheoryId id = theory::Theory::theoryOf(node);
    if(d_logic == "QF_AX" && id == theory::THEORY_UF) {
      id = theory::THEORY_ARRAY;
    }
    return id;
  }

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(const TypeNode& typeNode) {
    return d_theoryTable[theoryIdOf(typeNode)];
  }

  /**
   * Wrapper for theory::Theory::theoryOf() that implements the
   * array/EUF hack.
   */
  inline theory::TheoryId theoryIdOf(const TypeNode& typeNode) {
    theory::TheoryId id = theory::Theory::theoryOf(typeNode);
    if(d_logic == "QF_AX" && id == theory::THEORY_UF) {
      id = theory::THEORY_ARRAY;
    }
    return id;
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

    // Mark it as asserted in this context
    //
    // [MGD] removed for now, this appears to have a nontrivial
    // performance penalty
    // node.setAttribute(theory::Asserted(), true);

    // Get the atom
    TNode atom = node.getKind() == kind::NOT ? node[0] : node;

    // Again, equality is a special case
    if (atom.getKind() == kind::EQUAL) {
      if(d_logic == "QF_AX") {
        Trace("theory") << "TheoryEngine::assertFact QF_AX logic; everything goes to Arrays" << std::endl;
        d_theoryTable[theory::THEORY_ARRAY]->assertFact(node);
      } else {
        theory::Theory* theory = theoryOf(atom);
        Trace("theory") << "asserting " << node << " to " << theory->getId() << std::endl;
        theory->assertFact(node);
      }
    } else {
      theory::Theory* theory = theoryOf(atom);
      Trace("theory") << "asserting " << node << " to " << theory->getId() << std::endl;
      theory->assertFact(node);
    }
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
    if (atom.getKind() == kind::EQUAL) {
      if(d_logic == "QF_AX") {
        Trace("theory") << "TheoryEngine::assertFact QF_AX logic; everything goes to Arrays" << std::endl;
        d_theoryTable[theory::THEORY_ARRAY]->explain(node);
      } else {
        theoryOf(atom[0])->explain(node);
      }
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

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */
