/*********************                                                        */
/*! \file theory_uf_morgan.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of uninterpreted functions with
 ** equality
 **
 ** Implementation of the theory of uninterpreted functions with equality,
 ** based on CVC4's congruence closure module (which is in turn based on
 ** the Nieuwenhuis and Oliveras paper, Fast Congruence Closure and
 ** Extensions.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__MORGAN__THEORY_UF_MORGAN_H
#define __CVC4__THEORY__UF__MORGAN__THEORY_UF_MORGAN_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/morgan/union_find.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdlist.h"
#include "util/congruence_closure.h"

namespace CVC4 {
namespace theory {
namespace uf {
namespace morgan {

class TheoryUFMorgan : public TheoryUF {

private:

  class CongruenceChannel {
    TheoryUFMorgan* d_uf;

  public:
    CongruenceChannel(TheoryUFMorgan* uf) : d_uf(uf) {}
    void notifyCongruent(TNode a, TNode b) {
      d_uf->notifyCongruent(a, b);
    }
  };/* class CongruenceChannel */
  friend class CongruenceChannel;

  /**
   * List of all of the non-negated literals from the assertion queue.
   * This is used only for conflict generation.
   * This differs from pending as the program generates new equalities that
   * are not in this list.
   * This will probably be phased out in future version.
   */
  context::CDList<Node> d_assertions;

  /**
   * Our channel connected to the congruence closure module.
   */
  CongruenceChannel d_ccChannel;

  /**
   * Instance of the congruence closure module.
   */
  CongruenceClosure<CongruenceChannel, CongruenceOperator<kind::APPLY_UF> > d_cc;

  /**
   * Our union find for equalities.
   */
  UnionFind<TNode, TNodeHashFunction> d_unionFind;

  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > EqList;
  typedef context::CDMap<Node, EqList*, NodeHashFunction> EqLists;

  /** List of all disequalities this theory has seen. */
  EqLists d_disequalities;

  /** List of all (potential) equalities to be propagated. */
  EqLists d_equalities;

  Node d_conflict;

  Node d_trueNode, d_falseNode, d_trueEqFalseNode;

  // === STATISTICS ===
  /** time spent in check() */
  KEEP_STATISTIC(TimerStat,
                 d_checkTimer,
                 "theory::uf::morgan::checkTime");
  /** time spent in propagate() */
  KEEP_STATISTIC(TimerStat,
                 d_propagateTimer,
                 "theory::uf::morgan::propagateTime");

  /** time spent in explain() */
  KEEP_STATISTIC(TimerStat,
                 d_explainTimer,
                 "theory::uf::morgan::explainTime");
  /** time spent in staticLearning() */
  KEEP_STATISTIC(TimerStat,
                 d_staticLearningTimer,
                 "theory::uf::morgan::staticLearningTime");
  /** time spent in presolve() */
  KEEP_STATISTIC(TimerStat,
                 d_presolveTimer,
                 "theory::uf::morgan::presolveTime");
  /** number of UF conflicts */
  KEEP_STATISTIC(IntStat,
                 d_conflicts,
                 "theory::uf::morgan::conflicts", 0);
  /** number of UF propagations */
  KEEP_STATISTIC(IntStat,
                 d_propagations,
                 "theory::uf::morgan::propagations", 0);
  /** CC module expl length */
  WrappedStat<AverageStat> d_ccExplanationLength;
  /** CC module # skolem vars */
  WrappedStat<IntStat> d_ccNewSkolemVars;

public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUFMorgan(int id, context::Context* ctxt, OutputChannel& out);

  /** Destructor for UF theory, cleans up memory and statistics. */
  ~TheoryUFMorgan();

  /**
   * Registers a previously unseen [in this context] node n.
   * For TheoryUF, this sets up and maintains invaraints about
   * equivalence class data-structures.
   *
   * Overloads a void registerTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void registerTerm(TNode n);

  /**
   * Currently this does nothing.
   *
   * Overloads a void preRegisterTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void preRegisterTerm(TNode n);

  /**
   * Checks whether the set of literals provided to the theory is consistent.
   *
   * If this is called at any effort level, it computes the congruence closure
   * of all of the positive literals in the context.
   *
   * If this is called at full effort it checks if any of the negative literals
   * are inconsistent with the congruence closure.
   *
   * Overloads  void check(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void check(Effort level);

  /**
   * Rewrites a node in the theory of uninterpreted functions.
   * This is fairly basic and only ensures that atoms that are
   * unsatisfiable or a valid are rewritten to false or true respectively.
   */
  RewriteResponse postRewrite(TNode n, bool topLevel);

  /**
   * Propagates theory literals.
   *
   * Overloads void propagate(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void propagate(Effort level);

  /**
   * Explains a previously theory-propagated literal.
   *
   * Overloads void explain(TNode n, Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void explain(TNode n, Effort level);

  /**
   * The theory should only add (via .operator<< or .append()) to the
   * "learned" builder.  It is a conjunction to add to the formula at
   * the top-level and may contain other theories' contributions.
   */
  void staticLearning(TNode in, NodeBuilder<>& learned);

  /**
   * A Theory is called with presolve exactly one time per user
   * check-sat.  presolve() is called after preregistration,
   * rewriting, and Boolean propagation, (other theories'
   * propagation?), but the notified Theory has not yet had its
   * check() or propagate() method called.  A Theory may empty its
   * assertFact() queue using get().  A Theory can raise conflicts,
   * add lemmas, and propagate literals during presolve().
   */
  void presolve();

  /**
   * Notification sent to the Theory when the search restarts.
   */
  void notifyRestart();

  /**
   * Gets a theory value.
   *
   * Overloads Node getValue(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  Node getValue(TNode n, TheoryEngine* engine);

  std::string identify() const { return std::string("TheoryUFMorgan"); }

private:

  /** Constructs a conflict from an inconsistent disequality. */
  Node constructConflict(TNode diseq);

  inline TNode find(TNode a);
  inline TNode debugFind(TNode a) const;

  void appendToDiseqList(TNode of, TNode eq);
  void appendToEqList(TNode of, TNode eq);
  void addDisequality(TNode eq);
  void registerEqualityForPropagation(TNode eq);

  /**
   * Receives a notification from the congruence closure module that
   * two nodes have been merged into the same congruence class.
   */
  void notifyCongruent(TNode a, TNode b);

  /**
   * Internally handle a congruence, whether generated by the CC
   * module or from a theory check().  Merges the classes from a and b
   * and looks for a conflict.  If there is one, sets d_conflict.
   */
  void merge(TNode a, TNode b);

  void dump();

};/* class TheoryUFMorgan */

inline TNode TheoryUFMorgan::find(TNode a) {
  return d_unionFind.find(a);
}

inline TNode TheoryUFMorgan::debugFind(TNode a) const {
  return d_unionFind.debugFind(a);
}

}/* CVC4::theory::uf::morgan namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__MORGAN__THEORY_UF_MORGAN_H */
