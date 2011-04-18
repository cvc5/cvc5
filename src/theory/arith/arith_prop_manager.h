#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H
#define __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H

#include "theory/valuation.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/unate_propagator.h"
#include "theory/arith/delta_rational.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdmap.h"
#include "context/cdo.h"

#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace arith {

class PropManager {
private:
  context::CDList<TNode> d_propagated;
  context::CDO<uint32_t> d_propagatedPos;
  typedef context::CDMap<TNode, TNode, TNodeHashFunction> ExplainMap;

  ExplainMap d_explanationMap;

  context::CDList<Node> d_reasons;

public:

  PropManager(context::Context* c):
    d_propagated(c),
    d_propagatedPos(c, 0),
    d_explanationMap(c),
    d_reasons(c)
  { }

  bool isPropagated(TNode n) const {
    return d_explanationMap.find(n) != d_explanationMap.end();
  }

  void propagate(TNode n, Node reason) {
    Assert(!isPropagated(n));
    Assert(reason.getKind() == kind::AND);

    d_explanationMap.insert(n, reason);

    d_reasons.push_back(reason);
    d_propagated.push_back(n);

    //std::cout << n  << std::endl << "<="<< reason<< std::endl;
  }

  bool hasMorePropagations() const {
    return d_propagatedPos < d_propagated.size();
  }

  TNode getPropagation() {
    Assert(hasMorePropagations());
    TNode prop = d_propagated[d_propagatedPos];
    d_propagatedPos = d_propagatedPos + 1;
    return prop;
  }

  TNode explain(TNode n) const {
    Assert(isPropagated(n));
    ExplainMap::iterator p = d_explanationMap.find(n);
    return (*p).second;
  }

};/* class PropManager */

class ArithPropManager : public PropManager {
private:
  const ArithVarNodeMap& d_arithvarNodeMap;
  const ArithUnatePropagator& d_propagator;
  Valuation d_valuation;

public:
  ArithPropManager(context::Context* c,
                   const ArithVarNodeMap& map,
                   const ArithUnatePropagator& prop,
                   Valuation v):
    PropManager(c), d_arithvarNodeMap(map), d_propagator(prop), d_valuation(v)
  {}

  /**
   * Returns true if the node has a value in sat solver in the current context.
   * In debug mode this fails an Assert() if the node has a negative assignment.
   */
  bool isAsserted(TNode n) const;

  /** Returns true if a bound was added. */
  bool propagateArithVar(bool upperbound, ArithVar var, const DeltaRational& b, TNode reason);

  Node boundAsNode(bool upperbound, ArithVar var, const DeltaRational& b) const;

  Node strictlyWeakerLowerBound(TNode n) const{
    return d_propagator.getWeakerImpliedLowerBound(n);
  }
  Node strictlyWeakerUpperBound(TNode n) const{
    return d_propagator.getWeakerImpliedUpperBound(n);
  }


  //Node strictlyWeakerAssertedUpperBound(TNode n) const;
  //Node strictlyWeakerAssertedLowerBound(TNode n) const;

  Node strictlyWeakerAssertedUpperBound(ArithVar v, const DeltaRational& b) const;

  Node strictlyWeakerAssertedLowerBound(ArithVar v, const DeltaRational& b) const;

  Node getBestImpliedLowerBound(ArithVar v, const DeltaRational& b) const;
  Node getBestImpliedUpperBound(ArithVar v, const DeltaRational& b) const;

  bool hasStrongerLowerBound(TNode current) const;
  bool hasStrongerUpperBound(TNode current) const;

  bool containsLiteral(TNode n) const {
    return d_propagator.containsLiteral(n);
  }

private:
  class Statistics {
  public:
    IntStat d_propagateArithVarCalls;
    IntStat d_addedPropagation;
    IntStat d_alreadySetSatLiteral;
    IntStat d_alreadyPropagatedNode;

    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H */
