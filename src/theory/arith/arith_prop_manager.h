/*********************                                                        */
/*! \file arith_prop_manager.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H
#define __CVC4__THEORY__ARITH__ARITH_PROP_MANAGER_H

#include "theory/valuation.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_node_map.h"
#include "theory/arith/atom_database.h"
#include "theory/arith/delta_rational.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdmap.h"
#include "context/cdo.h"
#include "theory/rewriter.h"
#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace arith {

class PropManager {
public:
  struct PropUnit {
    // consequent <= antecedent
    // i.e. the antecedent is the explanation of the consequent.
    Node consequent;
    Node antecedent;
    bool flag;
    PropUnit(Node c, Node a, bool f) :
      consequent(c), antecedent(a), flag(f)
    {}
  };

private:
  context::CDList<PropUnit> d_propagated;
  context::CDO<uint32_t> d_propagatedPos;

  /* This maps the node a theory engine will request on an explain call to
   * to its corresponding PropUnit.
   * This is node is potentially both the consequent or Rewriter::rewrite(consequent).
   */
  typedef context::CDMap<Node, size_t, NodeHashFunction> ExplainMap;
  ExplainMap d_explanationMap;

  size_t getIndex(TNode n) const {
    Assert(isPropagated(n));
    return (*(d_explanationMap.find(n))).second;
  }

public:

  PropManager(context::Context* c):
    d_propagated(c),
    d_propagatedPos(c, 0),
    d_explanationMap(c)
  { }

  const PropUnit& getUnit(TNode n) const {
    return d_propagated[getIndex(n)];
  }

  bool isPropagated(TNode n) const {
    return d_explanationMap.find(n) != d_explanationMap.end();
  }

  bool isFlagged(TNode n) const {
    return getUnit(n).flag;
  }

  void propagate(TNode n, Node reason, bool flag) {
    Assert(!isPropagated(n));

    if(flag){
      Node rewritten =  Rewriter::rewrite(n);
      d_explanationMap.insert(rewritten, d_propagated.size());
    }else{
      //If !flag, then the rewriter is idempotent on n.
      Assert(Rewriter::rewrite(n) == n);
    }
    d_explanationMap.insert(n, d_propagated.size());
    d_propagated.push_back(PropUnit(n, reason, flag));

    Debug("ArithPropManager") << n  << std::endl << "<="<< reason<< std::endl;
  }

  bool hasMorePropagations() const {
    return d_propagatedPos < d_propagated.size();
  }

  const PropUnit& getNextPropagation() {
    Assert(hasMorePropagations());
    const PropUnit& prop = d_propagated[d_propagatedPos];
    d_propagatedPos = d_propagatedPos + 1;
    return prop;
  }

  TNode explain(TNode n) const {
    return getUnit(n).antecedent;
  }

};/* class PropManager */

class ArithPropManager : public PropManager {
private:
  const ArithVarNodeMap& d_arithvarNodeMap;
  const ArithAtomDatabase& d_atomDatabase;
  Valuation d_valuation;

public:
  ArithPropManager(context::Context* c,
                   const ArithVarNodeMap& map,
                   const ArithAtomDatabase& db,
                   Valuation v):
    PropManager(c), d_arithvarNodeMap(map), d_atomDatabase(db), d_valuation(v)
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
    return d_atomDatabase.getWeakerImpliedLowerBound(n);
  }
  Node strictlyWeakerUpperBound(TNode n) const{
    return d_atomDatabase.getWeakerImpliedUpperBound(n);
  }

  Node strictlyWeakerAssertedUpperBound(ArithVar v, const DeltaRational& b) const;

  Node strictlyWeakerAssertedLowerBound(ArithVar v, const DeltaRational& b) const;

  Node getBestImpliedLowerBound(ArithVar v, const DeltaRational& b) const;
  Node getBestImpliedUpperBound(ArithVar v, const DeltaRational& b) const;

  bool containsLiteral(TNode n) const {
    return d_atomDatabase.containsLiteral(n);
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
