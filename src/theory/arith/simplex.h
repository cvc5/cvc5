/*********************                                                        */
/*! \file simplex.h
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

#ifndef __CVC4__THEORY__ARITH__SIMPLEX_H
#define __CVC4__THEORY__ARITH__SIMPLEX_H

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arith_priority_queue.h"
#include "theory/arith/arithvar_set.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/arith_prop_manager.h"

#include "util/options.h"

#include "util/stats.h"

#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class SimplexDecisionProcedure {
private:

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithPartialModel& d_partialModel;

  Tableau& d_tableau;
  ArithPriorityQueue d_queue;

  ArithPropManager& d_propManager;

  ArithVar d_numVariables;

  std::queue<Node> d_delayedLemmas;

  PermissiveBackArithVarSet d_updatedBounds;
  PermissiveBackArithVarSet d_candidateBasics;

  ArithVarMultiset d_pivotsInRound;

  Rational d_ZERO;
  DeltaRational d_DELTA_ZERO;

public:
  SimplexDecisionProcedure(ArithPropManager& propManager,
                           ArithPartialModel& pm,
                           Tableau& tableau);


  /**
   * Assert*(n, orig) takes an bound n that is implied by orig.
   * and asserts that as a new bound if it is tighter than the current bound
   * and updates the value of a basic variable if needed.
   *
   * orig must be a literal in the SAT solver so that it can be used for
   * conflict analysis.
   *
   * x is the variable getting the new bound,
   * c is the value of the new bound.
   *
   * If this new bound is in conflict with the other bound,
   * a node describing this conflict is returned.
   * If this new bound is not in conflict, Node::null() is returned.
   */
  Node AssertLower(ArithVar x, const DeltaRational& c, TNode orig);
  Node AssertUpper(ArithVar x, const DeltaRational& c, TNode orig);
  Node AssertEquality(ArithVar x, const DeltaRational& c, TNode orig);

private:
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
  void pivotAndUpdate(ArithVar x_i, ArithVar x_j, DeltaRational& v);

private:
  /**
   * A PreferenceFunction takes a const ref to the SimplexDecisionProcedure,
   * and 2 ArithVar variables and returns one of the ArithVar variables potentially
   * using the internals of the SimplexDecisionProcedure.
   *
   * Both ArithVar must be non-basic in d_tableau.
   */
  typedef ArithVar (*PreferenceFunction)(const SimplexDecisionProcedure&, ArithVar, ArithVar);

  /**
   * minVarOrder is a PreferenceFunction for selecting the smaller of the 2 ArithVars.
   * This PreferenceFunction is used during the VarOrder stage of
   * updateInconsistentVars.
   */
  static ArithVar minVarOrder(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y);

  /**
   * minRowCount is a PreferenceFunction for selecting the variable with the smaller
   * row count in the tableau.
   *
   * This is a hueristic rule and should not be used
   * during the VarOrder stage of updateInconsistentVars.
   */
  static ArithVar minColLength(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y);
  /**
   * minBoundAndRowCount is a PreferenceFunction for preferring a variable
   * without an asserted bound over variables with an asserted bound.
   * If both have bounds or both do not have bounds,
   * the rule falls back to minRowCount(...).
   *
   * This is a hueristic rule and should not be used
   * during the VarOrder stage of updateInconsistentVars.
   */
  static ArithVar minBoundAndRowCount(const SimplexDecisionProcedure& simp, ArithVar x, ArithVar y);

public:
  /**
   * Tries to update the assignments of variables such that all of the
   * assignments are consistent with their bounds.
   *
   * This is done by searching through the tableau.
   * If all of the variables can be made consistent with their bounds
   * Node::null() is returned. Otherwise a minimized conflict is returned.
   *
   * If a conflict is found, changes to the assignments need to be reverted.
   *
   * Tableau pivoting is performed so variables may switch from being basic to
   * nonbasic and vice versa.
   *
   * Corresponds to the "check()" procedure in [Cav06].
   */
  Node updateInconsistentVars();
private:
  Node searchForFeasibleSolution(uint32_t maxIterations);

  enum SearchPeriod {BeforeDiffSearch, DuringDiffSearch, AfterDiffSearch, DuringVarOrderSearch, AfterVarOrderSearch};

  Node findConflictOnTheQueue(SearchPeriod period, bool returnFirst = true);


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
  template <bool lowerBound>  ArithVar selectSlack(ArithVar x_i, PreferenceFunction pf);
  ArithVar selectSlackLowerBound(ArithVar x_i, PreferenceFunction pf = minVarOrder) {
    return selectSlack<true>(x_i, pf);
  }
  ArithVar selectSlackUpperBound(ArithVar x_i, PreferenceFunction pf = minVarOrder) {
    return selectSlack<false>(x_i, pf);
  }
  /**
   * Returns the smallest basic variable whose assignment is not consistent
   * with its upper and lower bounds.
   */
  ArithVar selectSmallestInconsistentVar();


  /**
   * Exports either the explanation of an upperbound or a lower bound
   * of the basic variable basic, using the non-basic variables in the row.
   */
  template <bool upperBound>
  void explainNonbasics(ArithVar basic, NodeBuilder<>& output);
  void explainNonbasicsLowerBound(ArithVar basic, NodeBuilder<>& output){
    explainNonbasics<false>(basic, output);
  }
  void explainNonbasicsUpperBound(ArithVar basic, NodeBuilder<>& output){
    explainNonbasics<true>(basic, output);
  }

  Node deduceUpperBound(ArithVar basicVar);
  Node deduceLowerBound(ArithVar basicVar);

  /**
   * Given a non-basic variable that is know to not be updatable
   * to a consistent value, construct and return a conflict.
   * Follows section 4.2 in the CAV06 paper.
   */
  Node generateConflictAboveUpperBound(ArithVar conflictVar);
  Node generateConflictBelowLowerBound(ArithVar conflictVar);

public:
  /**
   * Checks to make sure the assignment is consistent with the tableau.
   * This code is for debugging.
   */
  void debugCheckTableau();
  void debugPivotSimplex(ArithVar x_i, ArithVar x_j);


  /**
   * Computes the value of a basic variable using the assignments
   * of the values of the variables in the basic variable's row tableau.
   * This can compute the value using either:
   * - the the current assignment (useSafe=false) or
   * - the safe assignment (useSafe = true).
   */
  DeltaRational computeRowValue(ArithVar x, bool useSafe);

  bool hasAnyUpdates() { return !d_updatedBounds.empty(); }
  void clearUpdates(){
    d_updatedBounds.purge();
  }
  void propagateCandidates();

  void increaseMax() {d_numVariables++;}

  /** Returns true if the simplex procedure has more delayed lemmas in its queue.*/
  bool hasMoreLemmas() const {
    return !d_delayedLemmas.empty();
  }
  /** Returns the next delayed lemmas on the queue.*/
  Node popLemma(){
    Assert(hasMoreLemmas());
    Node lemma = d_delayedLemmas.front();
    d_delayedLemmas.pop();
    return lemma;
  }

private:
  /** Adds a lemma to the queue. */
  void pushLemma(Node lemma){
    d_delayedLemmas.push(lemma);
    ++(d_statistics.d_delayedConflicts);
  }

  /** Adds a conflict as a lemma to the queue. */
  void delayConflictAsLemma(Node conflict){
   Node negatedConflict = negateConjunctionAsClause(conflict);
    pushLemma(negatedConflict);
  }

  template <bool above>
  inline bool isAcceptableSlack(int sgn, ArithVar nonbasic){
    return
      ( above && sgn < 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)) ||
      ( above && sgn > 0 && d_partialModel.strictlyAboveLowerBound(nonbasic)) ||
      (!above && sgn > 0 && d_partialModel.strictlyBelowUpperBound(nonbasic)) ||
      (!above && sgn < 0 && d_partialModel.strictlyAboveLowerBound(nonbasic));
  }

  /**
   * Checks a basic variable, b, to see if it is in conflict.
   * If a conflict is discovered a node summarizing the conflict is returned.
   * Otherwise, Node::null() is returned.
   */
  Node checkBasicForConflict(ArithVar b);

  Node weakenConflict(bool aboveUpper, ArithVar basicVar);
  TNode weakestExplanation(bool aboveUpper, DeltaRational& surplus, ArithVar v, const Rational& coeff, bool& anyWeakening, ArithVar basic);

  void propagateCandidate(ArithVar basic);
  bool propagateCandidateBound(ArithVar basic, bool upperBound);

  inline bool propagateCandidateLowerBound(ArithVar basic){
    return propagateCandidateBound(basic, false);
  }
  inline bool propagateCandidateUpperBound(ArithVar basic){
    return propagateCandidateBound(basic, true);
  }

  bool hasBounds(ArithVar basic, bool upperBound);
  bool hasLowerBounds(ArithVar basic){
    return hasBounds(basic, false);
  }
  bool hasUpperBounds(ArithVar basic){
    return hasBounds(basic, true);
  }
  DeltaRational computeBound(ArithVar basic, bool upperBound);

  inline DeltaRational computeLowerBound(ArithVar basic){
    return computeBound(basic, false);
  }
  inline DeltaRational computeUpperBound(ArithVar basic){
    return computeBound(basic, true);
  }


  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statPivots, d_statUpdates;

    IntStat d_statAssertUpperConflicts, d_statAssertLowerConflicts;
    IntStat d_statUpdateConflicts;

    TimerStat d_findConflictOnTheQueueTime;

    IntStat d_attemptBeforeDiffSearch, d_successBeforeDiffSearch;
    IntStat d_attemptAfterDiffSearch, d_successAfterDiffSearch;
    IntStat d_attemptDuringDiffSearch, d_successDuringDiffSearch;
    IntStat d_attemptDuringVarOrderSearch, d_successDuringVarOrderSearch;
    IntStat d_attemptAfterVarOrderSearch, d_successAfterVarOrderSearch;

    IntStat d_weakeningAttempts, d_weakeningSuccesses, d_weakenings;
    TimerStat d_weakenTime;

    TimerStat d_boundComputationTime;
    IntStat d_boundComputations, d_boundPropagations;

    IntStat d_delayedConflicts;

    TimerStat d_pivotTime;

    AverageStat d_avgNumRowsNotContainingOnUpdate;
    AverageStat d_avgNumRowsNotContainingOnPivot;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class SimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__SIMPLEX_H */

