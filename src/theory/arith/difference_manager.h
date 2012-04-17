

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H
#define __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H

#include "theory/arith/arithvar.h"
#include "theory/arith/constraint_forward.h"
#include "theory/uf/equality_engine.h"
#include "context/cdo.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "context/cdtrail_queue.h"
#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * This implements a CDMaybe.
 * This has either been set in the context or it has not.
 * T must have a default constructor and support assignment.
 */
template <class T>
class CDMaybe {
private:
  typedef std::pair<bool, T> BoolTPair;
  context::CDO<BoolTPair> d_data;

public:
  CDMaybe(context::Context* c) : d_data(c, std::make_pair(false, T()))
  {}

  bool isSet() const {
    return d_data.get().first;
  }

  void set(const T& d){
    Assert(!isSet());
    d_data.set(std::make_pair(true, d));
  }

  const T& get() const{
    Assert(isSet());
    return d_data.get().second;
  }
};

class DifferenceManager {
private:
  CDMaybe<Node> d_conflict;

  struct Difference {
    bool isSlack;
    TNode x;
    TNode y;
    Difference() : isSlack(false), x(TNode::null()),  y(TNode::null()){}
    Difference(TNode a, TNode b) : isSlack(true), x(a), y(b) {
      Assert(x < y);
    }
  };


  class DifferenceNotifyClass {
  private:
    DifferenceManager& d_dm;
  public:
    DifferenceNotifyClass(DifferenceManager& dm): d_dm(dm) {}

    bool notify(TNode propagation) {
      Debug("arith::differences") << "DifferenceNotifyClass::notify(" << propagation << ")" << std::endl;
      // Just forward to dm
      return d_dm.propagate(propagation);
    }

    void notify(TNode t1, TNode t2) {
      Debug("arith::differences") << "DifferenceNotifyClass::notify(" << t1 << ", " << t2 << ")" << std::endl;
      Node equality = t1.eqNode(t2);
      d_dm.propagate(equality);
    }
  };

  std::vector< Difference > d_differences;

  struct LiteralsQueueElem {
    bool d_eq;
    ArithVar d_var;
    Node d_reason;
    LiteralsQueueElem() : d_eq(false), d_var(ARITHVAR_SENTINEL), d_reason() {}
    LiteralsQueueElem(bool eq, ArithVar v, Node n) : d_eq(eq), d_var(v), d_reason(n) {}
  };

  /** Stores the queue of assertions. This keeps the Node backing the reasons */
  context::CDTrailQueue<LiteralsQueueElem> d_literalsQueue;
  //PropManager& d_queue;

  /** Store the propagations. */
  context::CDTrailQueue<Node> d_propagatations;

  /* This maps the node a theory engine will request on an explain call to
   * to its corresponding PropUnit.
   * This is node is potentially both the propagation or Rewriter::rewrite(propagation).
   */
  typedef context::CDHashMap<Node, size_t, NodeHashFunction> ExplainMap;
  ExplainMap d_explanationMap;

  ConstraintDatabase& d_constraintDatabase;
  TNodeCallBack& d_setupLiteral;

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
    size_t pos = (*(d_explanationMap.find(n))).second;
    return d_propagatations[pos];
  }

  void pushBack(TNode n){
    d_explanationMap.insert(n, d_propagatations.size());
    d_propagatations.enqueue(n);
  }

  void pushBack(TNode n, TNode r){
    d_explanationMap.insert(r, d_propagatations.size());
    d_explanationMap.insert(n, d_propagatations.size());
    d_propagatations.enqueue(n);
  }

  DifferenceNotifyClass d_notify;
  theory::uf::EqualityEngine<DifferenceNotifyClass> d_ee;

  bool propagate(TNode x);
  void explain(TNode literal, std::vector<TNode>& assumptions);

  Node d_false;

  /**
   * This is set to true when the first shared term is added.
   * When this is set to true in the context, d_queue is emptied
   * and not used again in the context.
   */
  context::CDO<bool> d_hasSharedTerms;


  /**
   * The generalization of asserting an equality or a disequality.
   * If there are shared equalities, this is added to the equality engine.
   * Otherwise, this is put on a queue until there is a shared term.
   */
  void assertLiteral(bool eq, ArithVar s, TNode reason);

  /** This sends a shared term to the uninterpretted equality engine. */
  void addAssertionToEqualityEngine(bool eq, ArithVar s, TNode reason);

  /** Dequeues the delay queue and asserts these equalities.*/
  void enableSharedTerms();
  void dequeueLiterals();

  void enqueueIntoNB(const std::set<TNode> all, NodeBuilder<>& nb);

  Node explainInternal(TNode internal);

public:

  DifferenceManager(context::Context* satContext, ConstraintDatabase&, TNodeCallBack&);

  Node explain(TNode literal);
  void explain(TNode lit, NodeBuilder<>& out);

  void addDifference(ArithVar s, Node x, Node y);

  inline bool isDifferenceSlack(ArithVar s) const{
    if(s < d_differences.size()){
      return d_differences[s].isSlack;
    }else{
      return false;
    }
  }

  /** Assert an equality. */
  void differenceIsZero(Constraint eq);

  /** Assert a conjunction from lb and ub. */
  void differenceIsZero(Constraint lb, Constraint ub);

  /** Assert that the value cannot be zero. */
  void differenceCannotBeZero(Constraint c);

  void addSharedTerm(Node x);
};/* class DifferenceManager */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H */

