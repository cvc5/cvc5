

#include "cvc4_private.h"

#pragma once

#include "theory/arith/arithvar.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/constraint_forward.h"

#include "theory/uf/equality_engine.h"

#include "context/cdo.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "context/cdtrail_queue.h"
#include "context/cdmaybe.h"

#include "util/stats.h"
#include "util/dense_map.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithCongruenceManager {
private:
  context::CDMaybe<Node> d_conflict;

  /**
   * The set of ArithVars equivalent to a pair of terms.
   * If this is 0 or cannot be 0, this can be signalled.
   * The pair of terms for the congruence is stored in watched equalities.
   */
  DenseSet d_watchedVariables;
  /** d_watchedVariables |-> (= x y) */
  ArithVarToNodeMap d_watchedEqualities;


  class ArithCongruenceNotify {
  private:
    ArithCongruenceManager& d_acm;
  public:
    ArithCongruenceNotify(ArithCongruenceManager& acm): d_acm(acm) {}

    bool notify(TNode propagation) {
      Debug("arith::congruences") << "ArithCongruenceNotify::notify(" << propagation << ")" << std::endl;
      // Just forward to dm
      return d_acm.propagate(propagation);
    }

    void notify(TNode t1, TNode t2) {
      Debug("arith::congruences") << "ArithCongruenceNotify::notify(" << t1 << ", " << t2 << ")" << std::endl;
      Node equality = t1.eqNode(t2);
      d_acm.propagate(equality);
    }
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
  TNodeCallBack& d_setupLiteral;

  const ArithVarNodeMap& d_av2Node;

  theory::uf::EqualityEngine<ArithCongruenceNotify> d_ee;
  Node d_false;

public:

  bool inConflict() const{
    return d_conflict.isSet();
  };

  Node conflict() const{
    Assert(inConflict());
    return d_conflict.get();
  }

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

  bool propagate(TNode x);
  void explain(TNode literal, std::vector<TNode>& assumptions);

  /**
   * This is set to true when the first shared term is added.
   * When this is set to true in the context, d_queue is emptied
   * and not used again in the context.
   */
  //context::CDO<bool> d_hasSharedTerms;


  /**
   * The generalization of asserting an equality or a disequality.
   * If there are shared equalities, this is added to the equality engine.
   * Otherwise, this is put on a queue until there is a shared term.
   */
  //void assertLiteral(bool eq, ArithVar s, TNode reason);

  /** This sends a shared term to the uninterpretted equality engine. */
  //void addAssertionToEqualityEngine(bool eq, ArithVar s, TNode reason);
  void assertionToEqualityEngine(bool eq, ArithVar s, TNode reason);

  /** Dequeues the delay queue and asserts these equalities.*/
  void enableSharedTerms();
  void dequeueLiterals();

  void enqueueIntoNB(const std::set<TNode> all, NodeBuilder<>& nb);

  Node explainInternal(TNode internal);

public:

  ArithCongruenceManager(context::Context* satContext, ConstraintDatabase&, TNodeCallBack&, const ArithVarNodeMap&);

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

};/* class CongruenceManager */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */


