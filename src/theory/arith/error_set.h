/*********************                                                        */
/*! \file error_set.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "cvc4_private.h"

#pragma once

#include <vector>

#include "options/arith_options.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/bound_counts.h"
#include "theory/arith/callbacks.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau_sizes.h"
#include "util/bin_heap.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {


/**
 * The priority queue has 3 different modes of operation:
 * - Collection
 *   This passively collects arithmetic variables that may be inconsistent.
 *   This does not maintain any heap structure.
 *   dequeueInconsistentBasicVariable() does not work in this mode!
 *   Entering this mode requires the queue to be empty.
 *
 * - Difference Queue
 *   This mode uses the difference between a variables and its bound
 *   to determine which to dequeue first.
 *
 * - Variable Order Queue
 *   This mode uses the variable order to determine which ArithVar is dequeued first.
 *
 * The transitions between the modes of operation are:
 *  Collection => Difference Queue
 *  Difference Queue => Variable Order Queue
 *  Difference Queue => Collection (queue must be empty!)
 *  Variable Order Queue => Collection (queue must be empty!)
 *
 * The queue begins in Collection mode.
 */


class ErrorSet;
class ErrorInfoMap;

class ComparatorPivotRule {
private:
  const ErrorSet* d_errorSet;

  options::ErrorSelectionRule d_rule;

 public:
  ComparatorPivotRule();
  ComparatorPivotRule(const ErrorSet* es, options::ErrorSelectionRule r);

  bool operator()(ArithVar v, ArithVar u) const;
  options::ErrorSelectionRule getRule() const { return d_rule; }
};

// typedef boost::heap::d_ary_heap<
//   ArithVar,
//   boost::heap::arity<2>,
//   boost::heap::compare<ComparatorPivotRule>,
//   boost::heap::mutable_<true> > FocusSet;
//
// typedef FocusSet::handle_type FocusSetHandle;

// typedef CVC4_PB_DS_NAMESPACE::priority_queue<
//   ArithVar,
//   ComparatorPivotRule,
//   CVC4_PB_DS_NAMESPACE::pairing_heap_tag> FocusSet;

// typedef FocusSet::point_iterator FocusSetHandle;

typedef BinaryHeap<ArithVar, ComparatorPivotRule> FocusSet;
typedef FocusSet::handle FocusSetHandle;


class ErrorInformation {
private:
  /** The variable that is in error. */
  ArithVar d_variable;

  /**
   * The constraint that was violated.
   * This needs to be saved in case that the
   * violated constraint
   */
  ConstraintP d_violated;

  /**
   * This is the sgn of the first derivate the variable must move to satisfy
   * the bound violated.
   * If d_sgn > 0, then d_violated was a lowerbound.
   * If d_sgn < 0, then d_violated was an upperbound.
   */
  int d_sgn;

  /**
   * If this is true, then the bound is no longer set on d_variables.
   * This MUST be undone before this is deleted.
   */
  bool d_relaxed;

  /**
   * If this is true, then the variable is in the focus set and the focus heap.
   * d_handle is then a reasonable thing to interpret.
   * If this is false, the variable is somewhere in
   */
  bool d_inFocus;
  FocusSetHandle d_handle;

  /**
   * Auxillary information for storing the difference between a variable and its bound.
   * Only set on signals.
   */
  DeltaRational* d_amount;

  /** */
  uint32_t d_metric;

public:
  ErrorInformation();
  ErrorInformation(ArithVar var, ConstraintP vio, int sgn);
  ~ErrorInformation();
  ErrorInformation(const ErrorInformation& ei);
  ErrorInformation& operator=(const ErrorInformation& ei);

  void reset(ConstraintP c, int sgn);

  inline ArithVar getVariable() const { return d_variable; }

  bool isRelaxed() const { return d_relaxed; }
  void setRelaxed()
  {
    Assert(!d_relaxed);
    d_relaxed = true;
  }
  void setUnrelaxed()
  {
    Assert(d_relaxed);
    d_relaxed = false;
  }

  inline int sgn() const { return d_sgn; }

  inline bool inFocus() const { return d_inFocus; }
  inline int focusSgn() const {
    return (d_inFocus) ? sgn() : 0;
  }

  inline void setInFocus(bool inFocus) { d_inFocus = inFocus; }

  const DeltaRational& getAmount() const {
    Assert(d_amount != NULL);
    return *d_amount;
  }

  void setAmount(const DeltaRational& am);
  void setMetric(uint32_t m) { d_metric = m; }
  uint32_t getMetric() const { return d_metric; }

  inline void setHandle(FocusSetHandle h) {
    Assert(d_inFocus);
    d_handle = h;
  }
  inline const FocusSetHandle& getHandle() const{ return d_handle; }

  inline ConstraintP getViolated() const { return d_violated; }

  bool debugInitialized() const {
    return
      d_variable != ARITHVAR_SENTINEL &&
      d_violated != NullConstraint &&
      d_sgn != 0;
  }
  void print(std::ostream& os) const {
    os << "{ErrorInfo: " << d_variable
       << ", " << d_violated
       << ", " << d_sgn
       << ", " << d_relaxed
       << ", " << d_inFocus;
    if(d_amount == NULL){
      os << "NULL";
    }else{
      os << (*d_amount);
    }
    os << "}";
  }
};

class ErrorInfoMap : public DenseMap<ErrorInformation> {};

class ErrorSet {
private:
  /**
   * Reference to the arithmetic partial model for checking if a variable
   * is consistent with its upper and lower bounds.
   */
  ArithVariables& d_variables;

  /**
   * The set of all variables that violate exactly one of their bounds.
   */
  ErrorInfoMap d_errInfo;

  options::ErrorSelectionRule d_selectionRule;
  /**
   * The ordered heap for the variables that are in ErrorSet.
   */
  FocusSet d_focus;


  /**
   * A strict subset of the error set.
   *   d_outOfFocus \neq d_errInfo.
   *
   * Its symbolic complement is Focus.
   *   d_outOfFocus \intersect Focus == \emptyset
   *   d_outOfFocus \union Focus == d_errInfo
   */
  ArithVarVec d_outOfFocus;

  /**
   * Before a variable is added to the error set, it is added to the signals list.
   * A variable may appear on the list multiple times.
   * This introduces a delay.
   */
  ArithVarVec d_signals;

  TableauSizes d_tableauSizes;

  BoundCountingLookup d_boundLookup;

  /**
   * Computes the difference between the assignment and its bound for x.
   */
public:
  DeltaRational computeDiff(ArithVar x) const;
private:
 void recomputeAmount(ErrorInformation& ei, options::ErrorSelectionRule r);

 void update(ErrorInformation& ei);
 void transitionVariableOutOfError(ArithVar v);
 void transitionVariableIntoError(ArithVar v);
 void addBackIntoFocus(ArithVar v);

public:

  /** The new focus set is the entire error set. */
  void blur();
  void dropFromFocus(ArithVar v);

  void dropFromFocusAll(const ArithVarVec& vec) {
    for(ArithVarVec::const_iterator i = vec.begin(), i_end = vec.end(); i != i_end; ++i){
      ArithVar v = *i;
      dropFromFocus(v);
    }
  }

  ErrorSet(ArithVariables& var, TableauSizes tabSizes, BoundCountingLookup boundLookup);

  typedef ErrorInfoMap::const_iterator error_iterator;
  error_iterator errorBegin() const { return d_errInfo.begin(); }
  error_iterator errorEnd() const { return d_errInfo.end(); }

  bool inError(ArithVar v) const { return d_errInfo.isKey(v); }
  bool inFocus(ArithVar v) const { return d_errInfo[v].inFocus(); }

  void pushErrorInto(ArithVarVec& vec) const;
  void pushFocusInto(ArithVarVec& vec) const;

  options::ErrorSelectionRule getSelectionRule() const;
  void setSelectionRule(options::ErrorSelectionRule rule);

  inline ArithVar topFocusVariable() const{
    Assert(!focusEmpty());
    return d_focus.top();
  }

  inline void signalVariable(ArithVar var){
    d_signals.push_back(var);
  }

  inline void signalUnderCnd(ArithVar var, bool b){
    if(b){ signalVariable(var); }
  }

  inline bool inconsistent(ArithVar var) const{
    return !d_variables.assignmentIsConsistent(var) ;
  }
  inline void signalIfInconsistent(ArithVar var){
    signalUnderCnd(var, inconsistent(var));
  }

  inline bool errorEmpty() const{
    return d_errInfo.empty();
  }
  inline uint32_t errorSize() const{
    return d_errInfo.size();
  }

  inline bool focusEmpty() const {
    return d_focus.empty();
  }
  inline uint32_t focusSize() const{
    return d_focus.size();
  }

  inline int getSgn(ArithVar x) const {
    Assert(inError(x));
    return d_errInfo[x].sgn();
  }
  inline int focusSgn(ArithVar v) const {
    if(inError(v)){
      return d_errInfo[v].focusSgn();
    }else{
      return 0;
    }
  }

  void focusDownToJust(ArithVar v);

  void clearFocus();

  /** Clears the set. */
  void clear();
  void reduceToSignals();

  bool noSignals() const {
    return d_signals.empty();
  }
  bool moreSignals() const {
    return !noSignals();
  }
  ArithVar topSignal() const {
    Assert(moreSignals());
    return d_signals.back();
  }

  /**
   * Moves a variable out of the signals.
   * This moves it into the error set.
   * Return the previous focus sign.
   */
  int popSignal();

  const DeltaRational& getAmount(ArithVar v) const {
    return d_errInfo[v].getAmount();
  }

  uint32_t sumMetric(ArithVar a) const{
    Assert(inError(a));
    BoundCounts bcs = d_boundLookup.atBounds(a);
    uint32_t count = getSgn(a) > 0 ? bcs.upperBoundCount() : bcs.lowerBoundCount();

    uint32_t length = d_tableauSizes.getRowLength(a);

    return (length - count);
  }

  uint32_t getMetric(ArithVar a) const {
    return d_errInfo[a].getMetric();
  }

  ConstraintP getViolated(ArithVar a) const {
    return d_errInfo[a].getViolated();
  }


  typedef FocusSet::const_iterator focus_iterator;
  focus_iterator focusBegin() const { return d_focus.begin(); }
  focus_iterator focusEnd() const { return d_focus.end(); }

  void debugPrint(std::ostream& out) const;

private:
  class Statistics {
  public:
    IntStat d_enqueues;
    IntStat d_enqueuesCollection;
    IntStat d_enqueuesDiffMode;
    IntStat d_enqueuesVarOrderMode;

    IntStat d_enqueuesCollectionDuplicates;
    IntStat d_enqueuesVarOrderModeDuplicates;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
