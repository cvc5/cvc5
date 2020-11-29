/*********************                                                        */
/*! \file partial_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datastructures that track variable by variable information.
 **
 ** This is a datastructure that tracks variable specific information.
 ** This is partially context dependent to back track upper/lower bounds
 ** and information derived from these.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__PARTIAL_MODEL_H
#define CVC4__THEORY__ARITH__PARTIAL_MODEL_H

#include <list>
#include <vector>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/bound_counts.h"
#include "theory/arith/callbacks.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/delta_rational.h"

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * (For the moment) the type hierarchy goes as:
 * Integer <: Real
 * The type number of a variable is an integer representing the most specific
 * type of the variable. The possible values of type number are:
 */
enum class ArithType {
  Unset,
  Real,
  Integer,
};

class ArithVariables {
private:

  class VarInfo {
    friend class ArithVariables;
    ArithVar d_var;

    DeltaRational d_assignment;
    ConstraintP d_lb;
    ConstraintP d_ub;
    int d_cmpAssignmentLB;
    int d_cmpAssignmentUB;

    unsigned d_pushCount;
    ArithType d_type;
    Node d_node;
    bool d_auxiliary;

  public:
    VarInfo();

    bool setAssignment(const DeltaRational& r, BoundsInfo& prev);
    bool setLowerBound(ConstraintP c, BoundsInfo& prev);
    bool setUpperBound(ConstraintP c, BoundsInfo& prev);

    /** Returns true if this VarInfo has been initialized. */
    bool initialized() const;

    /**
     * Initializes the VarInfo with the ArithVar index it is associated with,
     * the node that the variable represents, and whether it is an auxillary
     * variable.
     */
    void initialize(ArithVar v, Node n, bool aux);

    /** Uninitializes the VarInfo. */
    void uninitialize();

    bool canBeReclaimed() const;

    /** Indicator variables for if the assignment is equal to the upper
     * and lower bounds. */
    BoundCounts atBoundCounts() const;

    /** Combination of indicator variables for whether it has upper and
     * lower bounds.  */
    BoundCounts hasBoundCounts() const;

    /** Stores both atBoundCounts() and hasBoundCounts().  */
    BoundsInfo boundsInfo() const;
  };

  /**Maps from ArithVar -> VarInfo */
  typedef DenseMap<VarInfo> VarInfoVec;

  /** This maps an ArithVar to its Variable information.*/
  VarInfoVec d_vars;

  /** Partial Map from Arithvar -> PreviousAssignment */
  DenseMap<DeltaRational> d_safeAssignment;

  /** if d_vars.isKey(x), then x < d_numberOfVariables */
  ArithVar d_numberOfVariables;

  /** [0, d_numberOfVariables) \intersect d_vars.keys == d_pool */
  // Everything in the pool is fair game.
  // There must be NO outstanding assertions
  std::vector<ArithVar> d_pool;
  std::vector<ArithVar> d_released;
  //std::list<ArithVar>::iterator d_releasedIterator;

  // Reverse Map from Node to ArithVar
  // Inverse of d_vars[x].d_node
  NodeToArithVarMap d_nodeToArithVarMap;


  /** The queue of constraints where the assignment is at the bound.*/
  DenseMap<BoundsInfo> d_boundsQueue;

  /**
   * If this is true, record the incoming changes to the bound information.
   * If this is false, the responsibility of recording the changes is
   * LinearEqualities's.
   */
  bool d_enqueueingBoundCounts;

 public:

  /** Returns the number of variables. */
  ArithVar getNumberOfVariables() const;

  /** Returns true if the node has an associated variables. */
  bool hasArithVar(TNode x) const;

  /** Returns true if the variable has a defining node. */
  bool hasNode(ArithVar a) const;

  /** Returns the ArithVar associated with a node. */
  ArithVar asArithVar(TNode x) const;

  /** Returns the node associated with an ArithVar. */
  Node asNode(ArithVar a) const;

  /** Allocates a freshly allocated variables. */
  ArithVar allocateVariable();

  class var_iterator {
  private:
    const VarInfoVec* d_vars;
    VarInfoVec::const_iterator d_wrapped;
  public:
    var_iterator();
    var_iterator(const VarInfoVec* vars, VarInfoVec::const_iterator ci);
    var_iterator& operator++();

    bool operator==(const var_iterator& other) const;
    bool operator!=(const var_iterator& other) const;
    ArithVar operator*() const;

  private:
    void nextInitialized();
  };

  var_iterator var_begin() const;
  var_iterator var_end() const;


  bool canBeReleased(ArithVar v) const;
  void releaseArithVar(ArithVar v);
  void attemptToReclaimReleased();

  /** Is this variable guaranteed to have an integer assignment?
   * (Should agree with the type system.) */
  bool isInteger(ArithVar x) const;

  /** Is the assignment to x integral? */
  bool integralAssignment(ArithVar x) const;

  /* Is this variable defined as a linear sum of other variables? */
  bool isAuxiliary(ArithVar x) const;

  /* Is the variable both input and not auxiliary? */
  bool isIntegerInput(ArithVar x) const;

 private:

  typedef std::pair<ArithVar, ConstraintP> AVCPair;
  class LowerBoundCleanUp {
  private:
    ArithVariables* d_pm;
  public:
    LowerBoundCleanUp(ArithVariables* pm);
    void operator()(AVCPair* restore);
  };

  class UpperBoundCleanUp {
  private:
    ArithVariables* d_pm;
  public:
    UpperBoundCleanUp(ArithVariables* pm);
    void operator()(AVCPair* restore);
  };

  typedef context::CDList<AVCPair, LowerBoundCleanUp> LBReverts;
  LBReverts d_lbRevertHistory;

  typedef context::CDList<AVCPair, UpperBoundCleanUp> UBReverts;
  UBReverts d_ubRevertHistory;

  void pushUpperBound(VarInfo&);
  void popUpperBound(AVCPair*);
  void pushLowerBound(VarInfo&);
  void popLowerBound(AVCPair*);

  // This is true when setDelta() is called, until invalidateDelta is called
  bool d_deltaIsSafe;
  // Cache of a value of delta to ensure a total order.
  Rational d_delta;
  // Function to call if the value of delta needs to be recomputed.
  DeltaComputeCallback d_deltaComputingFunc;


public:

  ArithVariables(context::Context* c, DeltaComputeCallback deltaComputation);

  /**
   * This sets the lower bound for a variable in the current context.
   * This must be stronger the previous constraint.
   */
  void setLowerBoundConstraint(ConstraintP lb);

  /**
   * This sets the upper bound for a variable in the current context.
   * This must be stronger the previous constraint.
   */
  void setUpperBoundConstraint(ConstraintP ub);

  /** Returns the constraint for the upper bound of a variable. */
  inline ConstraintP getUpperBoundConstraint(ArithVar x) const{
    return d_vars[x].d_ub;
  }
  /** Returns the constraint for the lower bound of a variable. */
  inline ConstraintP getLowerBoundConstraint(ArithVar x) const{
    return d_vars[x].d_lb;
  }

  /* Initializes a variable to a safe value.*/
  void initialize(ArithVar x, Node n, bool aux);

  ArithVar allocate(Node n, bool aux = false);

  /* Gets the last assignment to a variable that is known to be consistent. */
  const DeltaRational& getSafeAssignment(ArithVar x) const;
  const DeltaRational& getAssignment(ArithVar x, bool safe) const;

  /* Reverts all variable assignments to their safe values. */
  void revertAssignmentChanges();

  /* Commits all variables assignments as safe.*/
  void commitAssignmentChanges();


  bool lowerBoundIsZero(ArithVar x);
  bool upperBoundIsZero(ArithVar x);

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

  inline int cmpAssignmentLowerBound(ArithVar x) const{
    return d_vars[x].d_cmpAssignmentLB;
  }
  inline int cmpAssignmentUpperBound(ArithVar x) const{
    return d_vars[x].d_cmpAssignmentUB;
  }

  inline BoundCounts atBoundCounts(ArithVar x) const {
    return d_vars[x].atBoundCounts();
  }
  inline BoundCounts hasBoundCounts(ArithVar x) const {
    return d_vars[x].hasBoundCounts();
  }
  inline BoundsInfo boundsInfo(ArithVar x) const{
    return d_vars[x].boundsInfo();
  }

  bool strictlyBelowUpperBound(ArithVar x) const;
  bool strictlyAboveLowerBound(ArithVar x) const;
  bool assignmentIsConsistent(ArithVar x) const;

  void printModel(ArithVar x, std::ostream& out) const;
  void printModel(ArithVar x) const;

  /** returns true iff x has both a lower and upper bound. */
  bool hasEitherBound(ArithVar x) const;
  inline bool hasLowerBound(ArithVar x) const{
    return d_vars[x].d_lb != NullConstraint;
  }
  inline bool hasUpperBound(ArithVar x) const{
    return d_vars[x].d_ub != NullConstraint;
  }

  const Rational& getDelta();

  void invalidateDelta();

  void setDelta(const Rational& d);

  void startQueueingBoundCounts();
  void stopQueueingBoundCounts();
  void addToBoundQueue(ArithVar v, const BoundsInfo& prev);

  BoundsInfo selectBoundsInfo(ArithVar v, bool old) const;

  bool boundsQueueEmpty() const;
  void processBoundsQueue(BoundUpdateCallback& changed);

  void printEntireModel(std::ostream& out) const;


  /**
   * Precondition: assumes boundsAreEqual(x).
   * If the either the lower/ upper bound is an equality, eq,
   * this returns make_pair(eq, NullConstraint).
   * Otherwise, this returns make_pair(lb, ub).
   */
  std::pair<ConstraintP, ConstraintP> explainEqualBounds(ArithVar x) const;

private:

  /**
   * This function implements the mostly identical:
   * revertAssignmentChanges() and commitAssignmentChanges().
   */
  void clearSafeAssignments(bool revert);

  bool debugEqualSizes();

  bool inMaps(ArithVar x) const;

};/* class ArithVariables */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__PARTIAL_MODEL_H */
