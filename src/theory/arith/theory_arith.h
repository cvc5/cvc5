/*********************                                                        */
/*! \file theory_arith.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Arithmetic theory.
 **
 ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdset.h"
#include "expr/node.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_set.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/unate_propagator.h"
#include "theory/arith/simplex.h"

#include "util/stats.h"

#include <vector>
#include <map>
#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * Implementation of QF_LRA.
 * Based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArith : public Theory {
private:

  /* TODO Everything in the chopping block needs to be killed. */
  /* Chopping block begins */

  std::vector<Node> d_splits;
  //This stores the eager splits sent out of the theory.

  /* Chopping block ends */

  std::vector<Node> d_variables;

  /**
   * If ArithVar v maps to the node n in d_removednode,
   * then n = (= asNode(v) rhs) where rhs is a term that
   * can be used to determine the value of n uysing getValue().
   */
  std::map<ArithVar, Node> d_removedRows;

  /**
   * Priority Queue of the basic variables that may be inconsistent.
   *
   * This is required to contain at least 1 instance of every inconsistent
   * basic variable. This is only required to be a superset though so its
   * contents must be checked to still be basic and inconsistent.
   */
  std::priority_queue<ArithVar> d_possiblyInconsistent;

  /** Stores system wide constants to avoid unnessecary reconstruction. */
  ArithConstants d_constants;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithPartialModel d_partialModel;

  /**
   * Set of ArithVars that were introduced via preregisteration.
   */
  ArithVarSet d_userVariables;

  /**
   * Bidirectional map between Nodes and ArithVars.
   */
  NodeToArithVarMap d_nodeToArithVarMap;
  ArithVarToNodeMap d_arithVarToNodeMap;

  inline bool hasArithVar(TNode x) const {
    return d_nodeToArithVarMap.find(x) != d_nodeToArithVarMap.end();
  }

  inline ArithVar asArithVar(TNode x) const{
    Assert(hasArithVar(x));
    Assert((d_nodeToArithVarMap.find(x))->second <= ARITHVAR_SENTINEL);
    return (d_nodeToArithVarMap.find(x))->second;
  }
  inline Node asNode(ArithVar a) const{
    Assert(d_arithVarToNodeMap.find(a) != d_arithVarToNodeMap.end());
    return (d_arithVarToNodeMap.find(a))->second;
  }

  inline void setArithVar(TNode x, ArithVar a){
    Assert(!hasArithVar(x));
    Assert(d_arithVarToNodeMap.find(a) == d_arithVarToNodeMap.end());
    d_arithVarToNodeMap[a] = x;
    d_nodeToArithVarMap[x] = a;
  }

  /**
   * List of all of the inequalities asserted in the current context.
   */
  context::CDSet<Node, NodeHashFunction> d_diseq;

  /**
   * The tableau for all of the constraints seen thus far in the system.
   */
  Tableau d_tableau;

  ArithUnatePropagator d_propagator;
  SimplexDecisionProcedure d_simplex;

public:
  TheoryArith(context::Context* c, OutputChannel& out);
  ~TheoryArith();

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);

  /** CD setup for a node. Currently does nothing. */
  void registerTerm(TNode n);

  void check(Effort e);
  void propagate(Effort e);
  void explain(TNode n);

  void notifyEq(TNode lhs, TNode rhs);

  Node getValue(TNode n, Valuation* valuation);

  void shutdown(){ }

  void presolve();

  void staticLearning(TNode in, NodeBuilder<>& learned);

  std::string identify() const { return std::string("TheoryArith"); }

private:

  ArithVar determineLeftVariable(TNode assertion, Kind simpleKind);


  /**
   * This requests a new unique ArithVar value for x.
   * This also does initial (not context dependent) set up for a variable,
   * except for setting up the initial.
   */
  ArithVar requestArithVar(TNode x, bool basic);

  /** Initial (not context dependent) sets up for a variable.*/
  void setupInitialValue(ArithVar x);

  /** Initial (not context dependent) sets up for a new slack variable.*/
  void setupSlack(TNode left);


  /**
   * Handles the case splitting for check() for a new assertion.
   * returns true if their is a conflict.
   */
  bool assertionCases(TNode assertion);

  /**
   * Returns the basic variable with the shorted row containg a non-basic variable.
   * If no such row exists, return ARITHVAR_SENTINEL.
   */
  ArithVar findShortestBasicRow(ArithVar variable);

  /**
   * Debugging only routine!
   * Returns true iff every variable is consistent in the partial model.
   */
  bool entireStateIsConsistent();

  /**
   * Permanently removes a variable from the problem.
   * The caller guarentees the saftey of this removal!
   */
  void permanentlyRemoveVariable(ArithVar v);


  void asVectors(Polynomial& p,
                 std::vector<Rational>& coeffs,
                 std::vector<ArithVar>& variables) const;


  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statUserVariables, d_statSlackVariables;
    IntStat d_statDisequalitySplits;
    IntStat d_statDisequalityConflicts;
    TimerStat d_staticLearningTimer;

    IntStat d_permanentlyRemovedVariables;
    TimerStat d_presolveTime;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;


};/* class TheoryArith */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */
