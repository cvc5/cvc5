

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H
#define __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H

#include "theory/arith/arith_utilities.h"
#include "theory/uf/equality_engine.h"
#include "context/cdo.h"
#include "context/cdlist.h"
#include "context/context.h"
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

  context::CDList<Node> d_reasons;
  PropManager& d_queue;


  DifferenceNotifyClass d_notify;
  theory::uf::EqualityEngine<DifferenceNotifyClass> d_ee;

  void propagate(TNode x);
  void explain(TNode literal, std::vector<TNode>& assumptions);

  Node d_false;

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

  void differenceIsZero(ArithVar s, TNode reason);

  void differenceCannotBeZero(ArithVar s, TNode reason);

  void addSharedTerm(Node x);
};/* class DifferenceManager */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__DIFFERENCE_MANAGER_H */

