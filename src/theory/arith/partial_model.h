/*********************                                                        */
/*! \file partial_model.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#include "expr/node.h"

#include "context/context.h"
#include "context/cdvector.h"
#include "context/cdo.h"

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/constraint_forward.h"


#include <vector>

#ifndef __CVC4__THEORY__ARITH__PARTIAL_MODEL_H
#define __CVC4__THEORY__ARITH__PARTIAL_MODEL_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithPartialModel {
private:

  unsigned d_mapSize;

  //Maps from ArithVar -> T
  std::vector<bool> d_hasSafeAssignment;
  std::vector<DeltaRational> d_assignment;
  std::vector<DeltaRational> d_safeAssignment;

  context::CDVector<Constraint> d_ubc;
  context::CDVector<Constraint> d_lbc;

  // This is true when setDelta() is called, until invalidateDelta is called
  bool d_deltaIsSafe;
  // Cache of a value of delta to ensure a total order.
  Rational d_delta;
  // Function to call if the value of delta needs to be recomputed.
  RationalCallBack& d_deltaComputingFunc;

  /**
   * List contains all of the variables that have an unsafe assignment.
   */
  typedef std::vector<ArithVar> HistoryList;
  HistoryList d_history;


public:

  ArithPartialModel(context::Context* c, RationalCallBack& deltaComputation);

  /**
   * This sets the lower bound for a variable in the current context.
   * This must be stronger the previous constraint.
   */
  void setLowerBoundConstraint(Constraint lb);

  /**
   * This sets the upper bound for a variable in the current context.
   * This must be stronger the previous constraint.
   */
  void setUpperBoundConstraint(Constraint ub);

  /** Returns the constraint for the upper bound of a variable. */
  inline Constraint getUpperBoundConstraint(ArithVar x) const{
    return d_ubc[x];
  }
  /** Returns the constraint for the lower bound of a variable. */
  inline Constraint getLowerBoundConstraint(ArithVar x) const{
    return d_lbc[x];
  }

  /**
   * This forces the lower bound for a variable to be relaxed in the current context.
   * This is done by forcing the lower bound to be NullConstraint.
   * This is an expert only operation! (See primal simplex for an example.)
   */
  void forceRelaxLowerBound(ArithVar x);

  /**
   * This forces the upper bound for a variable to be relaxed in the current context.
   * This is done by forcing the upper bound to be NullConstraint.
   * This is an expert only operation! (See primal simplex for an example.)
   */
  void forceRelaxUpperBound(ArithVar x);

  /* Initializes a variable to a safe value.*/
  void initialize(ArithVar x, const DeltaRational& r);

  /* Gets the last assignment to a variable that is known to be consistent. */
  const DeltaRational& getSafeAssignment(ArithVar x) const;
  const DeltaRational& getAssignment(ArithVar x, bool safe) const;

  /* Reverts all variable assignments to their safe values. */
  void revertAssignmentChanges();

  /* Commits all variables assignments as safe.*/
  void commitAssignmentChanges();


  inline bool lowerBoundIsZero(ArithVar x){
    return hasLowerBound(x) && getLowerBound(x).sgn() == 0;
  }

  inline bool upperBoundIsZero(ArithVar x){
    return hasUpperBound(x) && getUpperBound(x).sgn() == 0;
  }

  bool boundsAreEqual(ArithVar x) const;

  /* Sets an unsafe variable assignment */
  void setAssignment(ArithVar x, const DeltaRational& r);
  void setAssignment(ArithVar x, const DeltaRational& safe, const DeltaRational& r);


  /** Must know that the bound exists before calling this! */
  const DeltaRational& getUpperBound(ArithVar x) const;
  const DeltaRational& getLowerBound(ArithVar x) const;
  const DeltaRational& getAssignment(ArithVar x) const;


  bool equalsLowerBound(ArithVar x, const DeltaRational& c);
  bool equalsUpperBound(ArithVar x, const DeltaRational& c);

  /**
   * If lowerbound > - \infty:
   *   return getAssignment(x).cmp(getLowerBound(x))
   * If lowerbound = - \infty:
   *   return 1
   */
  int cmpToLowerBound(ArithVar x, const DeltaRational& c) const;

  inline bool strictlyLessThanLowerBound(ArithVar x, const DeltaRational& c) const{
    return cmpToLowerBound(x, c) < 0;
  }
  inline bool lessThanLowerBound(ArithVar x, const DeltaRational& c) const{
    return cmpToLowerBound(x, c) <= 0;
  }

  inline bool strictlyGreaterThanLowerBound(ArithVar x, const DeltaRational& c) const{
    return cmpToLowerBound(x, c) > 0;
  }

  inline bool greaterThanLowerBound(ArithVar x, const DeltaRational& c) const{
    return cmpToLowerBound(x, c) >= 0;
  }
  /**
   * If upperbound < \infty:
   *   return getAssignment(x).cmp(getUpperBound(x))
   * If upperbound = \infty:
   *   return -1
   */
  int cmpToUpperBound(ArithVar x, const DeltaRational& c) const;

  inline bool strictlyLessThanUpperBound(ArithVar x, const DeltaRational& c) const{
    return cmpToUpperBound(x, c) < 0;
  }

  inline bool lessThanUpperBound(ArithVar x, const DeltaRational& c) const{
    return cmpToUpperBound(x, c) <= 0;
  }

  inline bool strictlyGreaterThanUpperBound(ArithVar x, const DeltaRational& c) const{
    return cmpToUpperBound(x, c) > 0;
  }

  inline bool greaterThanUpperBound(ArithVar x, const DeltaRational& c) const{
    return cmpToUpperBound(x, c) >= 0;
  }


  bool strictlyBelowUpperBound(ArithVar x) const;
  bool strictlyAboveLowerBound(ArithVar x) const;
  bool assignmentIsConsistent(ArithVar x) const;

  void printModel(ArithVar x);

  /** returns true iff x has both a lower and upper bound. */
  bool hasEitherBound(ArithVar x) const;
  inline bool hasLowerBound(ArithVar x) const{
    return d_lbc[x] != NullConstraint;
  }
  inline bool hasUpperBound(ArithVar x) const{
    return d_ubc[x] != NullConstraint;
  }

  const Rational& getDelta();

  inline void invalidateDelta() {
    d_deltaIsSafe = false;
  }

  void setDelta(const Rational& d){
    d_delta = d;
    d_deltaIsSafe = true;
  }

private:

  /**
   * This function implements the mostly identical:
   * revertAssignmentChanges() and commitAssignmentChanges().
   */
  void clearSafeAssignments(bool revert);

  bool equalSizes();

  bool inMaps(ArithVar x) const{
    return x < d_mapSize;
  }

};/* class ArithPartialModel */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* __CVC4__THEORY__ARITH__PARTIAL_MODEL_H */
