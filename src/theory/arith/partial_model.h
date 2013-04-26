/*********************                                                        */
/*! \file partial_model.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "context/cdlist.h"


#include "theory/arith/arithvar.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/callbacks.h"
#include "theory/arith/bound_counts.h"


#include <vector>
#include <list>

#pragma once

namespace CVC4 {
namespace theory {
namespace arith {



class ArithVariables {
private:
  class VarInfo {
    friend class ArithVariables;
    ArithVar d_var;

    DeltaRational d_assignment;
    Constraint d_lb;
    Constraint d_ub;
    int d_cmpAssignmentLB;
    int d_cmpAssignmentUB;

    unsigned d_pushCount;
    ArithType d_type;
    Node d_node;
    bool d_slack;

  public:
    VarInfo();

    bool setAssignment(const DeltaRational& r, BoundCounts& prev);
    bool setLowerBound(Constraint c, BoundCounts& prev);
    bool setUpperBound(Constraint c, BoundCounts& prev);

    bool initialized() const {
      return d_var != ARITHVAR_SENTINEL;
    }
    void initialize(ArithVar v, Node n, bool slack);
    void uninitialize();

    bool canBeReclaimed() const{
      return d_pushCount == 0;
    }

    BoundCounts boundCounts() const {
      uint32_t lbIndc = (d_cmpAssignmentLB == 0) ? 1 : 0;
      uint32_t ubIndc = (d_cmpAssignmentUB == 0) ? 1 : 0;
      return BoundCounts(lbIndc, ubIndc);
    }
  };

  //Maps from ArithVar -> VarInfo
  typedef DenseMap<VarInfo> VarInfoVec;
  VarInfoVec d_vars;

  // Partial Map from Arithvar -> PreviousAssignment
  DenseMap<DeltaRational> d_safeAssignment;

  // if d_vars.isKey(x), then x < d_numberOfVariables
  ArithVar d_numberOfVariables;

  /** [0, d_numberOfVariables) \intersect d_vars.keys == d_pool */
  // Everything in the pool is fair game.
  // There must be NO outstanding assertions
  std::vector<ArithVar> d_pool;
  std::list<ArithVar> d_released;
  std::list<ArithVar>::iterator d_releasedIterator;

  // Reverse Map from Node to ArithVar
  // Inverse of d_vars[x].d_node
  NodeToArithVarMap d_nodeToArithVarMap;

  DenseMap<BoundCounts> d_atBoundsQueue;

 public:

  inline ArithVar getNumberOfVariables() const {
    return d_numberOfVariables;
  }

  inline bool hasArithVar(TNode x) const {
    return d_nodeToArithVarMap.find(x) != d_nodeToArithVarMap.end();
  }

  inline bool hasNode(ArithVar a) const {
    return d_vars.isKey(a);
  }

  inline ArithVar asArithVar(TNode x) const{
    Assert(hasArithVar(x));
    Assert((d_nodeToArithVarMap.find(x))->second <= ARITHVAR_SENTINEL);
    return (d_nodeToArithVarMap.find(x))->second;
  }


  inline Node asNode(ArithVar a) const{
    Assert(hasNode(a));
    return d_vars[a].d_node;
  }

  ArithVar allocateVariable();

  class var_iterator {
  private:
    const VarInfoVec* d_vars;
    VarInfoVec::const_iterator d_wrapped;
  public:
    var_iterator(){}
    var_iterator(const VarInfoVec* vars, VarInfoVec::const_iterator ci)
      : d_vars(vars), d_wrapped(ci)
    {
      nextInitialized();
    }

    var_iterator& operator++(){
      ++d_wrapped;
      nextInitialized();
      return *this;
    }
    bool operator==(const var_iterator& other) const{
      return d_wrapped == other.d_wrapped;
    }
    bool operator!=(const var_iterator& other) const{
      return d_wrapped != other.d_wrapped;
    }
    ArithVar operator*() const{
      return *d_wrapped;
    }
  private:
    void nextInitialized(){
      VarInfoVec::const_iterator end = d_vars->end();
      while(d_wrapped != end &&
            !((*d_vars)[*d_wrapped].initialized())){
        ++d_wrapped;
      }
    }
  };
  var_iterator var_begin() const {
    return var_iterator(&d_vars, d_vars.begin());
  }

  var_iterator var_end() const {
    return var_iterator(&d_vars, d_vars.end());
  }


  bool canBeReleased(ArithVar v) const;
  void releaseArithVar(ArithVar v);
  void attemptToReclaimReleased();

  bool isInteger(ArithVar x) const {
    return d_vars[x].d_type >= ATInteger;
  }
  bool isSlack(ArithVar x) const {
    return d_vars[x].d_slack;
  }
 private:

  typedef std::pair<ArithVar, Constraint> AVCPair;
  class LowerBoundCleanUp {
  private:
    ArithVariables* d_pm;
  public:
    LowerBoundCleanUp(ArithVariables* pm) : d_pm(pm) {}
    void operator()(AVCPair* restore);
  };

  class UpperBoundCleanUp {
  private:
    ArithVariables* d_pm;
  public:
    UpperBoundCleanUp(ArithVariables* pm) : d_pm(pm) {}
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

  bool d_enqueueingBoundCounts;

public:

  ArithVariables(context::Context* c, DeltaComputeCallback deltaComputation);

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
    return d_vars[x].d_ub;
  }
  /** Returns the constraint for the lower bound of a variable. */
  inline Constraint getLowerBoundConstraint(ArithVar x) const{
    return d_vars[x].d_lb;
  }

  /**
   * This forces the lower bound for a variable to be relaxed in the current context.
   * This is done by forcing the lower bound to be NullConstraint.
   * This is an expert only operation! (See primal simplex for an example.)
   */
  //void forceRelaxLowerBound(ArithVar x);

  /**
   * This forces the upper bound for a variable to be relaxed in the current context.
   * This is done by forcing the upper bound to be NullConstraint.
   * This is an expert only operation! (See primal simplex for an example.)
   */
  //void forceRelaxUpperBound(ArithVar x);

  /* Initializes a variable to a safe value.*/
  //void initialize(ArithVar x, const DeltaRational& r);
  void initialize(ArithVar x, Node n, bool slack);

  ArithVar allocate(Node n, bool slack = false);

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

  inline int cmpAssignmentLowerBound(ArithVar x) const{
    return d_vars[x].d_cmpAssignmentLB;
  }
  inline int cmpAssignmentUpperBound(ArithVar x) const{
    return d_vars[x].d_cmpAssignmentUB;
  }

  inline BoundCounts boundCounts(ArithVar x) const {
    return d_vars[x].boundCounts();
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

  inline void invalidateDelta() {
    d_deltaIsSafe = false;
  }

  void setDelta(const Rational& d){
    d_delta = d;
    d_deltaIsSafe = true;
  }

  // inline bool initialized(ArithVar x) const {
  //   return d_vars[x].initialized();
  // }

  void addToBoundQueue(ArithVar v, BoundCounts prev){
    if(d_enqueueingBoundCounts && !d_atBoundsQueue.isKey(v)){
      d_atBoundsQueue.set(v, prev);
    }
  }

  BoundCounts oldBoundCounts(ArithVar v) const {
    if(d_atBoundsQueue.isKey(v)){
      return d_atBoundsQueue[v];
    }else{
      return boundCounts(v);
    }
  }

  void startQueueingAtBoundQueue(){ d_enqueueingBoundCounts = true; }
  void stopQueueingAtBoundQueue(){ d_enqueueingBoundCounts = false; }

  void processAtBoundQueue(BoundCountsCallback& changed){
    while(!d_atBoundsQueue.empty()){
      ArithVar v = d_atBoundsQueue.back();
      BoundCounts prev = d_atBoundsQueue[v];
      d_atBoundsQueue.pop_back();
      BoundCounts curr = boundCounts(v);
      if(prev != curr){
        changed(v, prev);
      }
    }
  }

  void printEntireModel(std::ostream& out) const;

private:

  /**
   * This function implements the mostly identical:
   * revertAssignmentChanges() and commitAssignmentChanges().
   */
  void clearSafeAssignments(bool revert);

  bool debugEqualSizes();

  bool inMaps(ArithVar x) const{
    return x < getNumberOfVariables();
  }

};/* class ArithVariables */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

