

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H
#define __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H

#include "theory/arith/arith_utilities.h"
#include "theory/uf/equality_engine.h"
#include "context/cdo.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "context/cdtrail_queue.h"
#include "util/stats.h"
#include "theory/arith/arith_prop_manager.h"

namespace CVC4 {
namespace theory {
namespace arith {

class DifferenceManager {
private:
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
      d_dm.propagate(propagation);
      return true;
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
  PropManager& d_queue;


  DifferenceNotifyClass d_notify;
  theory::uf::EqualityEngine<DifferenceNotifyClass> d_ee;

  void propagate(TNode x);
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

public:

  DifferenceManager(context::Context*, PropManager&);

  Node explain(TNode literal);

  void addDifference(ArithVar s, Node x, Node y);

  inline bool isDifferenceSlack(ArithVar s) const{
    if(s < d_differences.size()){
      return d_differences[s].isSlack;
    }else{
      return false;
    }
  }

  void differenceIsZero(ArithVar s, TNode reason){
    assertLiteral(true, s, reason);
  }

  void differenceCannotBeZero(ArithVar s, TNode reason){
    assertLiteral(false, s, reason);
  }

  void addSharedTerm(Node x);
};/* class DifferenceManager */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H */

