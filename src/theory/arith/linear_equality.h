/*********************                                                        */
/*! \file linear_equality.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This module maintains the relationship between a Tableau and PartialModel.
 **
 ** This shares with the theory a Tableau, and a PartialModel that:
 **  - satisfies the equalities in the Tableau, and
 **  - the assignment for the non-basic variables satisfies their bounds.
 ** This maintains the relationship needed by the SimplexDecisionProcedure.
 **
 ** In the language of Simplex for DPLL(T), this provides:
 ** - update()
 ** - pivotAndUpdate()
 **
 ** This class also provides utility functions that require
 ** using both the Tableau and PartialModel.
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__LINEAR_EQUALITY_H
#define __CVC4__THEORY__ARITH__LINEAR_EQUALITY_H

#include "theory/arith/delta_rational.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/matrix.h"
#include "theory/arith/constraint.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {

class LinearEqualityModule {
private:
  /**
   * Manages information about the assignment and upper and lower bounds on the
   * variables.
   */
  ArithPartialModel& d_partialModel;

  /**
   * Reference to the Tableau to operate upon.
   */
  Tableau& d_tableau;

  /** Called whenever the value of a basic variable is updated. */
  ArithVarCallBack& d_basicVariableUpdates;

public:

  /**
   * Initializes a LinearEqualityModule with a partial model, a tableau,
   * and a callback function for when basic variables update their values.
   */
  LinearEqualityModule(ArithPartialModel& pm, Tableau& t, ArithVarCallBack& f):
    d_partialModel(pm), d_tableau(t), d_basicVariableUpdates(f)
  {}

  /**
   * Updates the assignment of a nonbasic variable x_i to v.
   * Also updates the assignment of basic variables accordingly.
   */
  void update(ArithVar x_i, const DeltaRational& v);

  /**
   * Updates the value of a basic variable x_i to v,
   * and then pivots x_i with the nonbasic variable in its row x_j.
   * Updates the assignment of the other basic variables accordingly.
   */
  void pivotAndUpdate(ArithVar x_i, ArithVar x_j, const DeltaRational& v);


  ArithPartialModel& getPartialModel() const{ return d_partialModel; }
  Tableau& getTableau() const{ return d_tableau; }


  bool hasBounds(ArithVar basic, bool upperBound);
  bool hasLowerBounds(ArithVar basic){
    return hasBounds(basic, false);
  }
  bool hasUpperBounds(ArithVar basic){
    return hasBounds(basic, true);
  }

private:
  /**
   * Exports either the explanation of an upperbound or a lower bound
   * of the basic variable basic, using the non-basic variables in the row.
   */
  template <bool upperBound>
  void propagateNonbasics(ArithVar basic, Constraint c);

public:
  void propagateNonbasicsLowerBound(ArithVar basic, Constraint c){
    Assert(c->isLowerBound());
    propagateNonbasics<false>(basic, c);
  }
  void propagateNonbasicsUpperBound(ArithVar basic, Constraint c){
    Assert(c->isUpperBound());
    propagateNonbasics<true>(basic, c);
  }

  /**
   * Computes the value of a basic variable using the assignments
   * of the values of the variables in the basic variable's row tableau.
   * This can compute the value using either:
   * - the the current assignment (useSafe=false) or
   * - the safe assignment (useSafe = true).
   */
  DeltaRational computeRowValue(ArithVar x, bool useSafe);

  inline DeltaRational computeLowerBound(ArithVar basic){
    return computeBound(basic, false);
  }
  inline DeltaRational computeUpperBound(ArithVar basic){
    return computeBound(basic, true);
  }

private:
  DeltaRational computeBound(ArithVar basic, bool upperBound);

public:
  /**
   * Checks to make sure the assignment is consistent with the tableau.
   * This code is for debugging.
   */
  void debugCheckTableau();

  /** Debugging information for a pivot. */
  void debugPivot(ArithVar x_i, ArithVar x_j);

  /**
   * 
   */
  bool debugEntireLinEqIsConsistent(const std::string& s);


private:
  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statPivots, d_statUpdates;

    TimerStat d_pivotTime;

    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;

};/* class LinearEqualityModule */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__LINEAR_EQUALITY_H */
