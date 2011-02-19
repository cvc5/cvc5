
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__SIMPLEX_H
#define __CVC4__THEORY__ARITH__SIMPLEX_H

#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar_set.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/partial_model.h"
#include "theory/output_channel.h"

#include "util/stats.h"

#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class SimplexDecisionProcedure {
private:
  typedef std::pair<ArithVar, DeltaRational> VarDRatPair;

  struct VarDRatPairCompare{
    inline bool operator()(const VarDRatPair& a, const VarDRatPair& b){
      return a.second > b.second;
    }
  };
  typedef std::priority_queue<VarDRatPair, std::vector<VarDRatPair>, VarDRatPairCompare> GriggioPQueue;

  GriggioPQueue d_griggioRuleQueue;

  /**
   * Priority Queue of the basic variables that may be inconsistent.
   *
   * This is required to contain at least 1 instance of every inconsistent
   * basic variable. This is only required to be a superset though so its
   * contents must be checked to still be basic and inconsistent.
   *
   * This is also required to agree with the row on variable order for termination.
   * Effectively this means that this must be a min-heap.
   */
  typedef std::priority_queue<ArithVar, vector<ArithVar>, std::greater<ArithVar> > PQueue;

  PQueue d_possiblyInconsistent;

  /** Stores system wide constants to avoid unnessecary reconstruction. */
  const ArithConstants& d_constants;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   */
  ArithPartialModel& d_partialModel;

  OutputChannel* d_out;

  Tableau& d_tableau;

  ArithVar d_numVariables;

  bool d_pivotStage;

public:
  SimplexDecisionProcedure(const ArithConstants& constants,
                           ArithPartialModel& pm,
                           OutputChannel* out,
                           Tableau& tableau) :
    d_possiblyInconsistent(),
    d_constants(constants),
    d_partialModel(pm),
    d_out(out),
    d_tableau(tableau),
    d_numVariables(0),
    d_pivotStage(true)
  {}

  void increaseMax() {d_numVariables++;}

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
  Node privateUpdateInconsistentVars();

  Node selectInitialConflict();

private:
  /**
   * Given the basic variable x_i,
   * this function finds the smallest nonbasic variable x_j in the row of x_i
   * in the tableau that can "take up the slack" to let x_i satisfy its bounds.
   * This returns TNode::null() if none exists.
   *
   * More formally one of the following conditions must be satisfied:
   * -  above && a_ij < 0 && assignment(x_j) < upperbound(x_j)
   * -  above && a_ij > 0 && assignment(x_j) > lowerbound(x_j)
   * - !above && a_ij > 0 && assignment(x_j) < upperbound(x_j)
   * - !above && a_ij < 0 && assignment(x_j) > lowerbound(x_j)
   */
  template <bool above>  ArithVar selectSlack(ArithVar x_i);

  ArithVar selectSlackBelow(ArithVar x_i) { return selectSlack<false>(x_i); }
  ArithVar selectSlackAbove(ArithVar x_i) { return selectSlack<true>(x_i);  }
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

private:
  /** Check to make sure all of the basic variables are within their bounds. */
  void checkBasicVariable(ArithVar basic);

  /**
   * Checks a basic variable, b, to see if it is in conflict.
   * If a conflict is discovered a node summarizing the conflict is returned.
   * Otherwise, Node::null() is returned.
   */
  Node checkBasicForConflict(ArithVar b);

  bool d_foundAConflict; // This field is used for statistics keeping ONLY!
  unsigned d_pivotsSinceConflict; // This field is used for statistics keeping ONLY!

  /** These fields are designed to be accessable to TheoryArith methods. */
  class Statistics {
  public:
    IntStat d_statPivots, d_statUpdates;

    IntStat d_statAssertUpperConflicts, d_statAssertLowerConflicts;
    IntStat d_statUpdateConflicts;
    IntStat d_statEarlyConflicts, d_statEarlyConflictImprovements;

    TimerStat d_selectInitialConflictTime;

    IntStat d_pivotsAfterConflict, d_checksWithWastefulPivots;
    TimerStat d_pivotTime;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class SimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__SIMPLEX_H */

