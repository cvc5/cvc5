/*********************                                                        */
/*! \file congruence_manager.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/arith/arithvar.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/partial_model.h"

#include "theory/uf/equality_engine.h"

#include "context/cdo.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "context/cdtrail_queue.h"
#include "context/cdmaybe.h"

#include "util/statistics_registry.h"
#include "util/dense_map.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithCongruenceManager {
private:
  context::CDRaised d_inConflict;
  RaiseConflict d_raiseConflict;

  /**
   * The set of ArithVars equivalent to a pair of terms.
   * If this is 0 or cannot be 0, this can be signalled.
   * The pair of terms for the congruence is stored in watched equalities.
   */
  DenseSet d_watchedVariables;
  /** d_watchedVariables |-> (= x y) */
  ArithVarToNodeMap d_watchedEqualities;


  class ArithCongruenceNotify : public eq::EqualityEngineNotify {
  private:
    ArithCongruenceManager& d_acm;
  public:
    ArithCongruenceNotify(ArithCongruenceManager& acm): d_acm(acm) {}

    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_acm.propagate(equality);
      } else {
        return d_acm.propagate(equality.notNode());
      }
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Unreachable();
    }

    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
      Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyTriggerTermEquality(" << t1 << ", " << t2 << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_acm.propagate(t1.eqNode(t2));
      } else {
        return d_acm.propagate(t1.eqNode(t2).notNode());
      }
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << std::endl;
      if (t1.getKind() == kind::CONST_BOOLEAN) {
        d_acm.propagate(t1.iffNode(t2));
      } else {
        d_acm.propagate(t1.eqNode(t2));
      }
    }

    void eqNotifyNewClass(TNode t) { }
    void eqNotifyPreMerge(TNode t1, TNode t2) { }
    void eqNotifyPostMerge(TNode t1, TNode t2) { }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
  };
  ArithCongruenceNotify d_notify;

  context::CDList<Node> d_keepAlive;

  /** Store the propagations. */
  context::CDTrailQueue<Node> d_propagatations;

  /* This maps the node a theory engine will request on an explain call to
   * to its corresponding PropUnit.
   * This is node is potentially both the propagation or
   * Rewriter::rewrite(propagation).
   */
  typedef context::CDHashMap<Node, size_t, NodeHashFunction> ExplainMap;
  ExplainMap d_explanationMap;

  ConstraintDatabase& d_constraintDatabase;
  SetupLiteralCallBack d_setupLiteral;

  const ArithVariables& d_avariables;

  eq::EqualityEngine d_ee;

  void raiseConflict(Node conflict){
    Assert(!inConflict());
    Debug("arith::conflict") << "difference manager conflict   " << conflict << std::endl;
    d_inConflict.raise();
    d_raiseConflict(conflict);
  }
public:

  bool inConflict() const{
    return d_inConflict.isRaised();
  };

  bool hasMorePropagations() const {
    return !d_propagatations.empty();
  }

  const Node getNextPropagation() {
    Assert(hasMorePropagations());
    Node prop = d_propagatations.front();
    d_propagatations.dequeue();
    return prop;
  }

  bool canExplain(TNode n) const {
    return d_explanationMap.find(n) != d_explanationMap.end();
  }

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

private:
  Node externalToInternal(TNode n) const{
    Assert(canExplain(n));
    ExplainMap::const_iterator iter = d_explanationMap.find(n);
    size_t pos = (*iter).second;
    return d_propagatations[pos];
  }

  void pushBack(TNode n){
    d_explanationMap.insert(n, d_propagatations.size());
    d_propagatations.enqueue(n);

    ++(d_statistics.d_propagations);
  }

  void pushBack(TNode n, TNode r){
    d_explanationMap.insert(r, d_propagatations.size());
    d_explanationMap.insert(n, d_propagatations.size());
    d_propagatations.enqueue(n);

    ++(d_statistics.d_propagations);
  }

  void pushBack(TNode n, TNode r, TNode w){
    d_explanationMap.insert(w, d_propagatations.size());
    d_explanationMap.insert(r, d_propagatations.size());
    d_explanationMap.insert(n, d_propagatations.size());
    d_propagatations.enqueue(n);

    ++(d_statistics.d_propagations);
  }

  bool propagate(TNode x);
  void explain(TNode literal, std::vector<TNode>& assumptions);


  /** This sends a shared term to the uninterpreted equality engine. */
  void assertionToEqualityEngine(bool eq, ArithVar s, TNode reason);

  /** Dequeues the delay queue and asserts these equalities.*/
  void enableSharedTerms();
  void dequeueLiterals();

  void enqueueIntoNB(const std::set<TNode> all, NodeBuilder<>& nb);

  Node explainInternal(TNode internal);

public:

  ArithCongruenceManager(context::Context* satContext, ConstraintDatabase&, SetupLiteralCallBack, const ArithVariables&, RaiseConflict raiseConflict);

  Node explain(TNode literal);
  void explain(TNode lit, NodeBuilder<>& out);

  void addWatchedPair(ArithVar s, TNode x, TNode y);

  inline bool isWatchedVariable(ArithVar s) const {
    return d_watchedVariables.isMember(s);
  }

  /** Assert an equality. */
  void watchedVariableIsZero(Constraint eq);

  /** Assert a conjunction from lb and ub. */
  void watchedVariableIsZero(Constraint lb, Constraint ub);

  /** Assert that the value cannot be zero. */
  void watchedVariableCannotBeZero(Constraint c);

  /** Assert that the value cannot be zero. */
  void watchedVariableCannotBeZero(Constraint c, Constraint d);


  /** Assert that the value is congruent to a constant. */
  void equalsConstant(Constraint eq);
  void equalsConstant(Constraint lb, Constraint ub);


  void addSharedTerm(Node x);

private:
  class Statistics {
  public:
    IntStat d_watchedVariables;
    IntStat d_watchedVariableIsZero;
    IntStat d_watchedVariableIsNotZero;

    IntStat d_equalsConstantCalls;

    IntStat d_propagations;
    IntStat d_propagateConstraints;
    IntStat d_conflicts;

    Statistics();
    ~Statistics();
  } d_statistics;

};/* class ArithCongruenceManager */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
