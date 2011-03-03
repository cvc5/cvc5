
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__SIMPLEX_H
#define __CVC4__THEORY__ARITH__SIMPLEX_H

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arith_priority_queue.h"
#include "theory/arith/arithvar_set.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/partial_model.h"
#include "theory/output_channel.h"

#include "util/options.h"

#include "util/stats.h"

#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {

class SimplexDecisionProcedure {
private:


  /** Stores system wide constants to avoid unnessecary reconstruction. */
  const ArithConstants& d_constants;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithPartialModel& d_partialModel;

  OutputChannel* d_out;

  Tableau& d_tableau;
  ArithPriorityQueue d_queue;

  ArithVar d_numVariables;

  std::vector<Node> d_delayedLemmas;
  uint32_t d_delayedLemmasPos;

public:
  SimplexDecisionProcedure(const ArithConstants& constants,
                           ArithPartialModel& pm,
                           OutputChannel* out,
                           Tableau& tableau) :
    d_constants(constants),
    d_partialModel(pm),
    d_out(out),
    d_tableau(tableau),
    d_queue(pm, tableau),
    d_numVariables(0),
    d_delayedLemmas(),
    d_delayedLemmasPos(0)
  {}


public:

  /**
   * Assert*(n, orig) takes an bound n that is implied by orig.
   * and asserts that as a new bound if it is tighter than the current bound
   * and updates the value of a basic variable if needed.
   * If this new bound is in conflict with the other bound,
   * a conflict is created and asserted to the output channel.
   *
   * orig must be an atom in the SAT solver so that it can be used for
   * conflict analysis.
   *
   * n is of the form (x =?= c) where x is a variable,
   * c is a constant and =?= is either LT, LEQ, EQ, GEQ, or GT.
   *
   * returns true if a conflict was asserted.
   */
  bool AssertLower(ArithVar x_i, const DeltaRational& c_i, TNode orig);
  bool AssertUpper(ArithVar x_i, const DeltaRational& c_i, TNode orig);
  bool AssertEquality(ArithVar x_i, const DeltaRational& c_i, TNode orig);

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
  template <bool limitIterations> Node searchForFeasibleSolution(uint32_t maxIterations);

  enum SearchPeriod {BeforeDiffSearch, AfterDiffSearch, DuringVarOrderSearch};

  Node findConflictOnTheQueue(SearchPeriod period);

private:
  /**
   * Given the basic variable x_i,
   * this function finds the smallest nonbasic variable x_j in the row of x_i
   * in the tableau that can "take up the slack" to let x_i satisfy its bounds.
   * This returns TNode::null() if none exists.
   *
   * If first is true, return the first ArithVar in the row to satisfy these conditions.
   * If first is false, return the ArithVar with the smallest row count.
   *
   * More formally one of the following conditions must be satisfied:
   * -  above && a_ij < 0 && assignment(x_j) < upperbound(x_j)
   * -  above && a_ij > 0 && assignment(x_j) > lowerbound(x_j)
   * - !above && a_ij > 0 && assignment(x_j) < upperbound(x_j)
   * - !above && a_ij < 0 && assignment(x_j) > lowerbound(x_j)
   */
  template <bool above>  ArithVar selectSlack(ArithVar x_i, bool first);
  ArithVar selectSlackBelow(ArithVar x_i, bool first) {
    return selectSlack<false>(x_i, first);
  }
  ArithVar selectSlackAbove(ArithVar x_i, bool first) {
    return selectSlack<true>(x_i, first);
  }
  /**
   * Returns the smallest basic variable whose assignment is not consistent
   * with its upper and lower bounds.
   */
  ArithVar selectSmallestInconsistentVar();

  /**
   * Given a non-basic variable that is know to not be updatable
   * to a consistent value, construct and return a conflict.
   * Follows section 4.2 in the CAV06 paper.
   */
  Node generateConflictAbove(ArithVar conflictVar);
  Node generateConflictBelow(ArithVar conflictVar);

public:
  void notifyOptions(const Options& opt){
    switch(opt.pivotRule){
    case Options::MINIMUM:
      d_queue.setPivotRule(ArithPriorityQueue::MINIMUM);
      break;
    case Options::BREAK_TIES:
      d_queue.setPivotRule(ArithPriorityQueue::BREAK_TIES);
      break;
    case Options::MAXIMUM:
      d_queue.setPivotRule(ArithPriorityQueue::MAXIMUM);
      break;
    default:
      Unhandled(opt.pivotRule);
    }
  }

  /**
   * Checks to make sure the assignment is consistent with the tableau.
   * This code is for debugging.
   */
  void checkTableau();

  /**
   * Computes the value of a basic variable using the assignments
   * of the values of the variables in the basic variable's row tableau.
   * This can compute the value using either:
   * - the the current assignment (useSafe=false) or
   * - the safe assignment (useSafe = true).
   */
  DeltaRational computeRowValue(ArithVar x, bool useSafe);


  void increaseMax() {d_numVariables++;}

  /** Returns true if the simplex procedure has more delayed lemmas in its queue.*/
  bool hasMoreLemmas() const {
    return d_delayedLemmasPos < d_delayedLemmas.size();
  }
  /** Returns the next delayed lemmas on the queue.*/
  Node popLemma(){
    Assert(hasMoreLemmas());
    Node lemma = d_delayedLemmas[d_delayedLemmasPos];
    ++d_delayedLemmasPos;
    return lemma;
  }

private:
  /** Adds a lemma to the queue. */
  void pushLemma(Node lemma){
    d_delayedLemmas.push_back(lemma);
    ++(d_statistics.d_delayedConflicts);
  }

  /** Adds a conflict as a lemma to the queue. */
  void delayConflictAsLemma(Node conflict){
    Node negatedConflict = negateConjunctionAsClause(conflict);
    pushLemma(negatedConflict);
  }

  /**
   * Checks a basic variable, b, to see if it is in conflict.
   * If a conflict is discovered a node summarizing the conflict is returned.
   * Otherwise, Node::null() is returned.
   */
  Node checkBasicForConflict(ArithVar b);

  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statPivots, d_statUpdates;

    IntStat d_statAssertUpperConflicts, d_statAssertLowerConflicts;
    IntStat d_statUpdateConflicts;

    TimerStat d_findConflictOnTheQueueTime;

    IntStat d_attemptBeforeDiffSearch, d_successBeforeDiffSearch;
    IntStat d_attemptAfterDiffSearch, d_successAfterDiffSearch;
    IntStat d_attemptDuringVarOrderSearch, d_successDuringVarOrderSearch;

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

