/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan, taking
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#include "expr/node.h"
#include "theory/theory.h"
#include "theory/theoryof_table.h"

#include "prop/prop_engine.h"
#include "theory/builtin/theory_builtin.h"
#include "theory/booleans/theory_bool.h"
#include "theory/uf/theory_uf.h"
#include "theory/arith/theory_arith.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"

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

  /** A table of Kinds to pointers to Theory */
  theory::TheoryOfTable d_theoryOfTable;

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

  public:

    EngineOutputChannel(TheoryEngine* engine, context::Context* context) :
      d_engine(engine),
      d_context(context),
      d_conflictNode(context),
      d_explanationNode(context){
    }

    void conflict(TNode conflictNode, bool safe) throw(theory::Interrupted, AssertionException) {
      Debug("theory") << "EngineOutputChannel::conflict(" << conflictNode << ")" << std::endl;
      d_conflictNode = conflictNode;
      ++(d_engine->d_statistics.d_statConflicts);
      if(safe) {
        throw theory::Interrupted();
      }
    }

    void propagate(TNode lit, bool) throw(theory::Interrupted, AssertionException) {
      d_propagatedLiterals.push_back(lit);
      ++(d_engine->d_statistics.d_statPropagate);
    }

    void lemma(TNode node, bool) throw(theory::Interrupted, AssertionException) {
      ++(d_engine->d_statistics.d_statLemma);
      d_engine->newLemma(node);
    }
    void augmentingLemma(TNode node, bool) throw(theory::Interrupted, AssertionException) {
      ++(d_engine->d_statistics.d_statAugLemma);
      d_engine->newAugmentingLemma(node);
    }
    void explanation(TNode explanationNode, bool) throw(theory::Interrupted, AssertionException) {
      d_explanationNode = explanationNode;
      ++(d_engine->d_statistics.d_statExplanation);
    }
  };



  EngineOutputChannel d_theoryOut;

  theory::builtin::TheoryBuiltin d_builtin;
  theory::booleans::TheoryBool d_bool;
  theory::uf::TheoryUF d_uf;
  theory::arith::TheoryArith d_arith;
  theory::arrays::TheoryArrays d_arrays;
  theory::bv::TheoryBV d_bv;

  /**
   * Check whether a node is in the pre-rewrite cache or not.
   */
  static bool inPreRewriteCache(TNode n, bool topLevel) throw() {
    return theory::Theory::inPreRewriteCache(n, topLevel);
  }

  /**
   * Get the value of the pre-rewrite cache (or Node::null()) if there is
   * none).
   */
  static Node getPreRewriteCache(TNode n, bool topLevel) throw() {
    return theory::Theory::getPreRewriteCache(n, topLevel);
  }

  /**
   * Set the value of the pre-rewrite cache.  v cannot be a null Node.
   */
  static void setPreRewriteCache(TNode n, bool topLevel, TNode v) throw() {
    return theory::Theory::setPreRewriteCache(n, topLevel, v);
  }

  /**
   * Check whether a node is in the post-rewrite cache or not.
   */
  static bool inPostRewriteCache(TNode n, bool topLevel) throw() {
    return theory::Theory::inPostRewriteCache(n, topLevel);
  }

  /**
   * Get the value of the post-rewrite cache (or Node::null()) if there is
   * none).
   */
  static Node getPostRewriteCache(TNode n, bool topLevel) throw() {
    return theory::Theory::getPostRewriteCache(n, topLevel);
  }

  /**
   * Set the value of the post-rewrite cache.  v cannot be a null Node.
   */
  static void setPostRewriteCache(TNode n, bool topLevel, TNode v) throw() {
    return theory::Theory::setPostRewriteCache(n, topLevel, v);
  }

  /**
   * This is the top rewrite entry point, called during preprocessing.
   * It dispatches to the proper theories to rewrite the given Node.
   */
  Node rewrite(TNode in, bool topLevel = true);

  /**
   * Replace ITE forms in a node.
   */
  Node removeITEs(TNode t);

public:

  /**
   * Construct a theory engine.
   */
  TheoryEngine(context::Context* ctxt) :
    d_propEngine(NULL),
    d_theoryOut(this, ctxt),
    d_builtin(ctxt, d_theoryOut),
    d_bool(ctxt, d_theoryOut),
    d_uf(ctxt, d_theoryOut),
    d_arith(ctxt, d_theoryOut),
    d_arrays(ctxt, d_theoryOut),
    d_bv(ctxt, d_theoryOut),
    d_statistics() {

    d_theoryOfTable.registerTheory(&d_builtin);
    d_theoryOfTable.registerTheory(&d_bool);
    d_theoryOfTable.registerTheory(&d_uf);
    d_theoryOfTable.registerTheory(&d_arith);
    d_theoryOfTable.registerTheory(&d_arrays);
    d_theoryOfTable.registerTheory(&d_bv);
  }

  void setPropEngine(prop::PropEngine* propEngine)
  {
    Assert(d_propEngine == NULL);
    d_propEngine = propEngine;
  }

  /**
   * This is called at shutdown time by the SmtEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory.
   */
  void shutdown() {
    d_builtin.shutdown();
    d_bool.shutdown();
    d_uf.shutdown();
    d_arith.shutdown();
    d_arrays.shutdown();
    d_bv.shutdown();
  }

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  theory::Theory* theoryOf(TNode n);

  /**
   * Preprocess a node.  This involves theory-specific rewriting, then
   * calling preRegisterTerm() on what's left over.
   * @param n the node to preprocess
   */
  Node preprocess(TNode n);

  /**
   * Assert the formula to the apropriate theory.
   * @param node the assertion
   */
  inline void assertFact(TNode node) {
    Debug("theory") << "TheoryEngine::assertFact(" << node << ")" << std::endl;
    theory::Theory* theory =
      node.getKind() == kind::NOT ? theoryOf(node[0]) : theoryOf(node);
    if(theory != NULL) {
      theory->assertFact(node);
    }
  }

  /**
   * Check all (currently-active) theories for conflicts.
   * @param effort the effort level to use
   */
  inline bool check(theory::Theory::Effort effort)
  {
    d_theoryOut.d_conflictNode = Node::null();
    d_theoryOut.d_propagatedLiterals.clear();
    // Do the checking
    try {
      //d_builtin.check(effort);
      //d_bool.check(effort);
      d_uf.check(effort);
      d_arith.check(effort);
      d_arrays.check(effort);
      //d_bv.check(effort);
    } catch(const theory::Interrupted&) {
      Debug("theory") << "TheoryEngine::check() => conflict" << std::endl;
    }
    // Return wheather we have a conflict
    return d_theoryOut.d_conflictNode.get().isNull();
  }

  inline const std::vector<TNode>& getPropagatedLiterals() const {
    return d_theoryOut.d_propagatedLiterals;
  }

  void clearPropagatedLiterals() {
    d_theoryOut.d_propagatedLiterals.clear();
  }

  inline void newLemma(TNode node) {
    d_propEngine->assertLemma(node);
  }

  inline void newAugmentingLemma(TNode node) {
    Node preprocessed = preprocess(node);
    d_propEngine->assertFormula(preprocessed);
  }

  /**
   * Returns the last conflict (if any).
   */
  inline Node getConflict() {
    return d_theoryOut.d_conflictNode;
  }

  inline void propagate() {
    d_theoryOut.d_propagatedLiterals.clear();
    // Do the propagation
    //d_builtin.propagate(theory::Theory::FULL_EFFORT);
    //d_bool.propagate(theory::Theory::FULL_EFFORT);
    d_uf.propagate(theory::Theory::FULL_EFFORT);
    d_arith.propagate(theory::Theory::FULL_EFFORT);
    d_arrays.propagate(theory::Theory::FULL_EFFORT);
    //d_bv.propagate(theory::Theory::FULL_EFFORT);
  }

  inline Node getExplanation(TNode node){
    d_theoryOut.d_explanationNode = Node::null();
    theory::Theory* theory =
              node.getKind() == kind::NOT ? theoryOf(node[0]) : theoryOf(node);
    theory->explain(node);
    return d_theoryOut.d_explanationNode;
  }

private:
  class Statistics {
  public:
    IntStat d_statConflicts, d_statPropagate, d_statLemma, d_statAugLemma, d_statExplanation;
    Statistics():
      d_statConflicts("theory::conflicts",0),
      d_statPropagate("theory::propagate",0),
      d_statLemma("theory::lemma",0),
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
