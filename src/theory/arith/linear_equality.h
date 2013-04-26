/*********************                                                        */
/*! \file linear_equality.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

#pragma once

#include "theory/arith/delta_rational.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "theory/arith/constraint_forward.h"
#include "theory/arith/simplex_update.h"
#include "theory/arith/options.h"

#include "util/maybe.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {

struct Border{
  // The constraint for the border
  Constraint d_bound;

  // The change to the nonbasic to reach the border
  DeltaRational d_diff;

  // Is reach this value fixing the constraint
  // or is going past this value hurting the constraint
  bool d_areFixing;

  // Entry into the tableau
  const Tableau::Entry* d_entry;

  // Was this an upper bound or a lower bound?
  bool d_upperbound;

  Border():
    d_bound(NullConstraint) // ignore the other values
  {}

  Border(Constraint l, const DeltaRational& diff, bool areFixing, const Tableau::Entry* en, bool ub):
    d_bound(l), d_diff(diff), d_areFixing(areFixing), d_entry(en),  d_upperbound(ub)
  {}

  Border(Constraint l, const DeltaRational& diff, bool areFixing, bool ub):
    d_bound(l), d_diff(diff), d_areFixing(areFixing), d_entry(NULL),  d_upperbound(ub)
  {}
  bool operator<(const Border& other) const{
    return d_diff < other.d_diff;
  }

  /** d_lim is the nonbasic variable's own bound. */
  bool ownBorder() const { return d_entry == NULL; }

  bool isZero() const { return d_diff.sgn() == 0; }
  static bool nonZero(const Border& b) { return !b.isZero(); }

  const Rational& getCoefficient() const {
    Assert(!ownBorder());
    return d_entry->getCoefficient();
  }
  void output(std::ostream& out) const;
};

inline std::ostream& operator<<(std::ostream& out, const Border& b){
  b.output(out);
  return out;
}

typedef std::vector<Border> BorderVec;

class BorderHeap {
  const int d_dir;

  class BorderHeapCmp {
  private:
    int d_nbDirection;
  public:
    BorderHeapCmp(int dir): d_nbDirection(dir){}
    bool operator()(const Border& a, const Border& b) const{
      if(d_nbDirection > 0){
        // if nb is increasing,
        //  this needs to act like a max
        //  in order to have a min heap
        return b < a;
      }else{
        // if nb is decreasing,
        //  this needs to act like a min
        //  in order to have a max heap
        return a < b;
      }
    }
  };
  const BorderHeapCmp d_cmp;

  BorderVec d_vec;

  BorderVec::iterator d_begin;

  /**
   * Once this is initialized the top of the heap will always
   * be at d_end - 1
   */
  BorderVec::iterator d_end;

  int d_possibleFixes;
  int d_numZeroes;

public:
  BorderHeap(int dir)
  : d_dir(dir), d_cmp(dir), d_possibleFixes(0), d_numZeroes(0)
  {}

  void push_back(const Border& b){
    d_vec.push_back(b);
    if(b.d_areFixing){
      d_possibleFixes++;
    }
    if(b.d_diff.sgn() == 0){
      d_numZeroes++;
    }
  }

  int numZeroes() const { return d_numZeroes; }
  int possibleFixes() const { return d_possibleFixes; }
  int direction() const { return d_dir; }

  void make_heap(){
    d_begin = d_vec.begin();
    d_end = d_vec.end();
    std::make_heap(d_begin, d_end, d_cmp);
  }

  void dropNonZeroes(){
    std::remove_if(d_vec.begin(), d_vec.end(), &Border::nonZero);
  }

  const Border& top() const {
    Assert(more());
    return *d_begin;
  }
  void pop_heap(){
    Assert(more());

    std::pop_heap(d_begin, d_end, d_cmp);
    --d_end;
  }

  BorderVec::const_iterator end() const{
    return BorderVec::const_iterator(d_end);
  }
  BorderVec::const_iterator begin() const{
    return BorderVec::const_iterator(d_begin);
  }

  inline bool more() const{ return d_begin != d_end; }

  inline bool empty() const{ return d_vec.empty(); }

  void clear(){
    d_possibleFixes = 0;
    d_numZeroes = 0;
    d_vec.clear();
  }
};





class LinearEqualityModule {
public:
  typedef ArithVar (LinearEqualityModule::*VarPreferenceFunction)(ArithVar, ArithVar) const;


  typedef bool (LinearEqualityModule::*UpdatePreferenceFunction)(const UpdateInfo&, const UpdateInfo&) const;

private:
  /**
   * Manages information about the assignment and upper and lower bounds on the
   * variables.
   */
  ArithVariables& d_variables;

  /** Reference to the Tableau to operate upon. */
  Tableau& d_tableau;

  /** Called whenever the value of a basic variable is updated. */
  BasicVarModelUpdateCallBack d_basicVariableUpdates;

  BorderHeap d_increasing;
  BorderHeap d_decreasing;
  Maybe<DeltaRational> d_upperBoundDifference;
  Maybe<DeltaRational> d_lowerBoundDifference;

public:

  /**
   * Initializes a LinearEqualityModule with a partial model, a tableau,
   * and a callback function for when basic variables update their values.
   */
  LinearEqualityModule(ArithVariables& vars, Tableau& t, BoundCountingVector& boundTracking, BasicVarModelUpdateCallBack f);

  /**
   * Updates the assignment of a nonbasic variable x_i to v.
   * Also updates the assignment of basic variables accordingly.
   */
  void updateUntracked(ArithVar x_i, const DeltaRational& v);
  void updateTracked(ArithVar x_i, const DeltaRational& v);
  void update(ArithVar x_i, const DeltaRational& v){
    if(d_areTracking){
      updateTracked(x_i,v);
    }else{
      updateUntracked(x_i,v);
    }
  }
  void updateMany(const DenseMap<DeltaRational>& many);

  /**
   * Updates the value of a basic variable x_i to v,
   * and then pivots x_i with the nonbasic variable in its row x_j.
   * Updates the assignment of the other basic variables accordingly.
   */
  void pivotAndUpdate(ArithVar x_i, ArithVar x_j, const DeltaRational& v);
  //void pivotAndUpdateAdj(ArithVar x_i, ArithVar x_j, const DeltaRational& v);

  ArithVariables& getVariables() const{ return d_variables; }
  Tableau& getTableau() const{ return d_tableau; }

  void forceNewBasis(const DenseSet& newBasis);

  bool hasBounds(ArithVar basic, bool upperBound);
  bool hasLowerBounds(ArithVar basic){
    return hasBounds(basic, false);
  }
  bool hasUpperBounds(ArithVar basic){
    return hasBounds(basic, true);
  }

  void startTrackingBoundCounts();
  void stopTrackingBoundCounts();


  void includeBoundCountChange(ArithVar nb, BoundCounts prev);

  void computeSafeUpdate(UpdateInfo& inf, VarPreferenceFunction basic);


  uint32_t updateProduct(const UpdateInfo& inf) const;

  inline bool minNonBasicVarOrder(const UpdateInfo& a, const UpdateInfo& b) const{
    return a.nonbasic() >= b.nonbasic();
  }

  /**
   * Prefer the update that touch the fewest entries in the matrix.
   *
   * The intuition is that this operation will be cheaper.
   * This strongly biases the system towards updates instead of pivots.
   */
  inline bool minProduct(const UpdateInfo& a, const UpdateInfo& b) const{
    uint32_t aprod = updateProduct(a);
    uint32_t bprod = updateProduct(b);

    if(aprod == bprod){
      return minNonBasicVarOrder(a,b);
    }else{
      return aprod > bprod;
    }
  }
  inline bool constrainedMin(const UpdateInfo& a, const UpdateInfo& b) const{
    if(a.describesPivot() && b.describesPivot()){
      bool aAtBounds = basicsAtBounds(a);
      bool bAtBounds = basicsAtBounds(b);
      if(aAtBounds != bAtBounds){
        return bAtBounds;
      }
    }
    return minProduct(a,b);
  }

  /**
   * If both a and b are pivots, prefer the pivot with the leaving variables that has equal bounds.
   * The intuition is that such variables will be less likely to lead to future problems.
   */
  inline bool preferFrozen(const UpdateInfo& a, const UpdateInfo& b) const {
    if(a.describesPivot() && b.describesPivot()){
      bool aFrozen = d_variables.boundsAreEqual(a.leaving());
      bool bFrozen = d_variables.boundsAreEqual(b.leaving());

      if(aFrozen != bFrozen){
        return bFrozen;
      }
    }
    return constrainedMin(a,b);
  }

  /**
   * Prefer pivots with entering variables that do not have bounds.
   * The intuition is that such variables will be less likely to lead to future problems.
   */
  bool preferNeitherBound(const UpdateInfo& a, const UpdateInfo& b) const {
    if(d_variables.hasEitherBound(a.nonbasic()) == d_variables.hasEitherBound(b.nonbasic())){
      return preferFrozen(a,b);
    }else{
      return d_variables.hasEitherBound(a.nonbasic());
    }
  }

  // template<bool heuristic>
  // bool preferNonDegenerate(const UpdateInfo& a, const UpdateInfo& b) const{
  //   if(a.focusDirection() == b.focusDirection()){
  //     if(heuristic){
  //       return preferNeitherBound(a,b);
  //     }else{
  //       return minNonBasicVarOrder(a,b);
  //     }
  //   }else{
  //     return a.focusDirection() < b.focusDirection();
  //   }
  // }

  // template <bool heuristic>
  // bool preferErrorsFixed(const UpdateInfo& a, const UpdateInfo& b) const{
  //   if( a.errorsChange() == b.errorsChange() ){
  //     return preferNonDegenerate<heuristic>(a,b);
  //   }else{
  //     return a.errorsChange() > b.errorsChange();
  //   }
  // }

  // template <bool heuristic>
  // bool preferConflictFound(const UpdateInfo& a, const UpdateInfo& b) const{
  //   if(a.d_foundConflict && b.d_foundConflict){
  //     // if both are true, determinize the preference
  //     return minNonBasicVarOrder(a,b);
  //   }else if( a.d_foundConflict || b.d_foundConflict ){
  //     return b.d_foundConflict;
  //   }else{
  //     return preferErrorsFixed<heuristic>(a,b);
  //   }
  // }

  bool modifiedBlands(const UpdateInfo& a, const UpdateInfo& b) const {
    Assert(a.focusDirection() == 0 && b.focusDirection() == 0);
    Assert(a.describesPivot());
    Assert(b.describesPivot());
    if(a.nonbasic() == b.nonbasic()){
      bool aIsZero = a.nonbasicDelta().sgn() == 0;
      bool bIsZero = b.nonbasicDelta().sgn() == 0;

      if((aIsZero || bIsZero) && (!aIsZero || !bIsZero)){
        return bIsZero;
      }else{
        return a.leaving() >= b.leaving();
      }
    }else{
      return a.nonbasic() > b.nonbasic();
    }
  }

  template <bool heuristic>
  bool preferWitness(const UpdateInfo& a, const UpdateInfo& b) const{
    WitnessImprovement aImp = a.getWitness(!heuristic);
    WitnessImprovement bImp = b.getWitness(!heuristic);

    if(aImp == bImp){
      switch(aImp){
      case ConflictFound:
        return preferNeitherBound(a,b);
      case ErrorDropped:
        if(a.errorsChange() == b.errorsChange()){
          return preferNeitherBound(a,b);
        }else{
          return a.errorsChange() > b.errorsChange();
        }
      case FocusImproved:
        return preferNeitherBound(a,b);
      case BlandsDegenerate:
        Assert(a.describesPivot());
        Assert(b.describesPivot());
        Assert(a.focusDirection() == 0 && b.focusDirection() == 0);
        return modifiedBlands(a,b);
      case HeuristicDegenerate:
        Assert(a.describesPivot());
        Assert(b.describesPivot());
        Assert(a.focusDirection() == 0 && b.focusDirection() == 0);
        return preferNeitherBound(a,b);
      case AntiProductive:
        return minNonBasicVarOrder(a, b);
      // Not valid responses
      case Degenerate:
      case FocusShrank:
        Unreachable();
      }
      Unreachable();
    }else{
      return aImp > bImp;
    }
  }

private:
  typedef std::vector<const Tableau::Entry*> EntryPointerVector;
  EntryPointerVector d_relevantErrorBuffer;

  //uint32_t computeUnconstrainedUpdate(ArithVar nb, int sgn,  DeltaRational& am);
  //uint32_t computedFixed(ArithVar nb, int sgn, const DeltaRational& am);
  void computedFixed(UpdateInfo&);

  // RowIndex -> BoundCount
  BoundCountingVector& d_boundTracking;
  bool d_areTracking;

  /**
   * Exports either the explanation of an upperbound or a lower bound
   * of the basic variable basic, using the non-basic variables in the row.
   */
  template <bool upperBound>
  void propagateNonbasics(ArithVar basic, Constraint c);

public:
  void propagateNonbasicsLowerBound(ArithVar basic, Constraint c){
    propagateNonbasics<false>(basic, c);
  }
  void propagateNonbasicsUpperBound(ArithVar basic, Constraint c){
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

  /**
   * A PreferenceFunction takes a const ref to the SimplexDecisionProcedure,
   * and 2 ArithVar variables and returns one of the ArithVar variables
   * potentially using the internals of the SimplexDecisionProcedure.
   */

  ArithVar noPreference(ArithVar x, ArithVar y) const{
    return x;
  }

  /**
   * minVarOrder is a PreferenceFunction for selecting the smaller of the 2
   * ArithVars. This PreferenceFunction is used during the VarOrder stage of
   * findModel.
   */
  ArithVar minVarOrder(ArithVar x, ArithVar y) const;

  /**
   * minColLength is a PreferenceFunction for selecting the variable with the
   * smaller row count in the tableau.
   *
   * This is a heuristic rule and should not be used during the VarOrder
   * stage of findModel.
   */
  ArithVar minColLength(ArithVar x, ArithVar y) const;

  /**
   * minRowLength is a PreferenceFunction for selecting the variable with the
   * smaller row count in the tableau.
   *
   * This is a heuristic rule and should not be used during the VarOrder
   * stage of findModel.
   */
  ArithVar minRowLength(ArithVar x, ArithVar y) const;

  /**
   * minBoundAndRowCount is a PreferenceFunction for preferring a variable
   * without an asserted bound over variables with an asserted bound.
   * If both have bounds or both do not have bounds,
   * the rule falls back to minRowCount(...).
   *
   * This is a heuristic rule and should not be used during the VarOrder
   * stage of findModel.
   */
  ArithVar minBoundAndColLength(ArithVar x, ArithVar y) const;


  template <bool above>
  inline bool isAcceptableSlack(int sgn, ArithVar nonbasic) const {
    return
      ( above && sgn < 0 && d_variables.strictlyBelowUpperBound(nonbasic)) ||
      ( above && sgn > 0 && d_variables.strictlyAboveLowerBound(nonbasic)) ||
      (!above && sgn > 0 && d_variables.strictlyBelowUpperBound(nonbasic)) ||
      (!above && sgn < 0 && d_variables.strictlyAboveLowerBound(nonbasic));
  }

  /**
   * Given the basic variable x_i,
   * this function finds the smallest nonbasic variable x_j in the row of x_i
   * in the tableau that can "take up the slack" to let x_i satisfy its bounds.
   * This returns ARITHVAR_SENTINEL if none exists.
   *
   * More formally one of the following conditions must be satisfied:
   * -  lowerBound && a_ij < 0 && assignment(x_j) < upperbound(x_j)
   * -  lowerBound && a_ij > 0 && assignment(x_j) > lowerbound(x_j)
   * - !lowerBound && a_ij > 0 && assignment(x_j) < upperbound(x_j)
   * - !lowerBound && a_ij < 0 && assignment(x_j) > lowerbound(x_j)
   *
   */
  template <bool lowerBound>  ArithVar selectSlack(ArithVar x_i, VarPreferenceFunction pf) const;
  ArithVar selectSlackLowerBound(ArithVar x_i, VarPreferenceFunction pf) const {
    return selectSlack<true>(x_i, pf);
  }
  ArithVar selectSlackUpperBound(ArithVar x_i, VarPreferenceFunction pf) const {
    return selectSlack<false>(x_i, pf);
  }

  const Tableau::Entry* selectSlackEntry(ArithVar x_i, bool above) const;

  inline bool basicIsTracked(ArithVar v) const {
    return d_boundTracking.isKey(v);
  }
  void trackVariable(ArithVar x_i);

  void maybeRemoveTracking(ArithVar v){
    Assert(!d_tableau.isBasic(v));
    if(d_boundTracking.isKey(v)){
      d_boundTracking.remove(v);
    }
  }

  // void trackVariable(ArithVar x_i){
  //   Assert(!basicIsTracked(x_i));
  //   d_boundTracking.set(x_i,computeBoundCounts(x_i));
  // }
  bool basicsAtBounds(const UpdateInfo& u) const;
private:
  BoundCounts computeBoundCounts(ArithVar x_i) const;
public:
  //BoundCounts cachingCountBounds(ArithVar x_i) const;
  BoundCounts _countBounds(ArithVar x_i) const;
  void trackingCoefficientChange(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn);

  void trackingSwap(ArithVar basic, ArithVar nb, int sgn);

  bool nonbasicsAtLowerBounds(ArithVar x_i) const;
  bool nonbasicsAtUpperBounds(ArithVar x_i) const;

  ArithVar _anySlackLowerBound(ArithVar x_i) const {
    return selectSlack<true>(x_i, &LinearEqualityModule::noPreference);
  }
  ArithVar _anySlackUpperBound(ArithVar x_i) const {
    return selectSlack<false>(x_i, &LinearEqualityModule::noPreference);
  }

private:
  class TrackingCallback : public CoefficientChangeCallback {
  private:
    LinearEqualityModule* d_linEq;
  public:
    TrackingCallback(LinearEqualityModule* le) : d_linEq(le) {}
    void update(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn){
      d_linEq->trackingCoefficientChange(ridx, nb, oldSgn, currSgn);
    }
    void swap(ArithVar basic, ArithVar nb, int oldNbSgn){
      d_linEq->trackingSwap(basic, nb, oldNbSgn);
    }
    bool canUseRow(RowIndex ridx) const {
      ArithVar basic = d_linEq->getTableau().rowIndexToBasic(ridx);
      return d_linEq->basicIsTracked(basic);
    }
 } d_trackCallback;

  /**
   * Selects the constraint for the variable v on the row for basic
   * with the weakest possible constraint that is consistent with the surplus
   * surplus.
   */
  Constraint weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v,
                                const Rational& coeff, bool& anyWeakening, ArithVar basic) const;

public:
  /**
   * Constructs a minimally weak conflict for the basic variable basicVar.
   */
  Node minimallyWeakConflict(bool aboveUpper, ArithVar basicVar) const;

  /**
   * Given a non-basic variable that is know to have a conflict on it,
   * construct and return a conflict.
   * Follows section 4.2 in the CAV06 paper.
   */
  inline Node generateConflictAboveUpperBound(ArithVar conflictVar) const {
    return minimallyWeakConflict(true, conflictVar);
  }

  inline Node generateConflictBelowLowerBound(ArithVar conflictVar) const {
    return minimallyWeakConflict(false, conflictVar);
  }

private:
  DeltaRational computeBound(ArithVar basic, bool upperBound);

public:
  void substitutePlusTimesConstant(ArithVar to, ArithVar from, const Rational& mult);
  void directlyAddToCoefficient(ArithVar row, ArithVar col, const Rational& mult);


  /**
   * Checks to make sure the assignment is consistent with the tableau.
   * This code is for debugging.
   */
  void debugCheckTableau();

  void debugCheckTracking();

  /** Debugging information for a pivot. */
  void debugPivot(ArithVar x_i, ArithVar x_j);

  /** Checks the tableau + partial model for consistency. */
  bool debugEntireLinEqIsConsistent(const std::string& s);


  ArithVar minBy(const ArithVarVec& vec, VarPreferenceFunction pf) const;

  /**
   * Returns true if there would be a conflict on this row after a pivot
   * and update using its basic variable and one of the non-basic variables on
   * the row.
   */
  bool willBeInConflictAfterPivot(const Tableau::Entry& entry, const DeltaRational& nbDiff, bool bToUB) const;
  UpdateInfo mkConflictUpdate(const Tableau::Entry& entry, bool ub) const;

  /**
   * Looks more an update for fcSimplex on the nonbasic variable nb with the focus coefficient.
   */
  UpdateInfo speculativeUpdate(ArithVar nb, const Rational& focusCoeff, UpdatePreferenceFunction pref);

private:

  /**
   * Examines the effects of pivoting the entries column variable
   * with the row's basic variable and setting the variable s.t.
   * the basic variable is equal to one of its bounds.
   *
   * If ub, then the basic variable will be equal its upper bound.
   * If not ub,then the basic variable will be equal its lower bound.
   *
   * Returns iff this row will be in conflict after the pivot.
   *
   * If this is false, add the bound to the relevant heap.
   * If the bound is +/-infinity, this is ignored.

   *
   * Returns true if this would be a conflict.
   * If it returns false, this
   */
  bool accumulateBorder(const Tableau::Entry& entry, bool ub);

  void handleBorders(UpdateInfo& selected, ArithVar nb, const Rational& focusCoeff, BorderHeap& heap, int minimumFixes, UpdatePreferenceFunction pref);
  void pop_block(BorderHeap& heap, int& brokenInBlock, int& fixesRemaining, int& negErrorChange);
  void clearSpeculative();
  Rational updateCoefficient(BorderVec::const_iterator startBlock, BorderVec::const_iterator endBlock);

private:
  /** These fields are designed to be accessible to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statPivots, d_statUpdates;
    TimerStat d_pivotTime;
    TimerStat d_adjTime;

    IntStat d_weakeningAttempts, d_weakeningSuccesses, d_weakenings;
    TimerStat d_weakenTime;

    Statistics();
    ~Statistics();
  };
  mutable Statistics d_statistics;

};/* class LinearEqualityModule */

struct Cand {
  ArithVar d_nb;
  uint32_t d_penalty;
  int d_sgn;
  const Rational* d_coeff;

  Cand(ArithVar nb, uint32_t penalty, int s, const Rational* c) :
    d_nb(nb), d_penalty(penalty), d_sgn(s), d_coeff(c){}
};


class CompPenaltyColLength {
private:
  LinearEqualityModule* d_mod;
public:
  CompPenaltyColLength(LinearEqualityModule* mod): d_mod(mod){}

  bool operator()(const Cand& x, const Cand& y) const {
    if(x.d_penalty == y.d_penalty || !options::havePenalties()){
      return x.d_nb == d_mod->minBoundAndColLength(x.d_nb,y.d_nb);
    }else{
      return x.d_penalty < y.d_penalty;
    }
  }
};

class UpdateTrackingCallback : public BoundCountsCallback {
private:
  LinearEqualityModule* d_mod;
public:
  UpdateTrackingCallback(LinearEqualityModule* mod): d_mod(mod){}
  void operator()(ArithVar v, BoundCounts bc){
    d_mod->includeBoundCountChange(v, bc);
  }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
