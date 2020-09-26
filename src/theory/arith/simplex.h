/*********************                                                        */
/*! \file simplex.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is an implementation of the Simplex Module for the Simplex for DPLL(T)
 ** decision procedure.
 **
 ** This implements the Simplex module for the Simpelx for DPLL(T) decision procedure.
 ** See the Simplex for DPLL(T) technical report for more background.(citation?)
 ** This shares with the theory a Tableau, and a PartialModel that:
 **  - satisfies the equalities in the Tableau, and
 **  - the assignment for the non-basic variables satisfies their bounds.
 ** This is required to either produce a conflict or satisifying PartialModel.
 ** Further, we require being told when a basic variable updates its value.
 **
 ** During the Simplex search we maintain a queue of variables.
 ** The queue is required to contain all of the basic variables that voilate their bounds.
 ** As elimination from the queue is more efficient to be done lazily,
 ** we do not maintain that the queue of variables needs to be only basic variables or only
 ** variables that satisfy their bounds.
 **
 ** The simplex procedure roughly follows Alberto's thesis. (citation?)
 ** There is one round of selecting using a heuristic pivoting rule. (See PreferenceFunction
 ** Documentation for the available options.)
 ** The non-basic variable is the one that appears in the fewest pivots. (Bruno says that
 ** Leonardo invented this first.)
 ** After this, Bland's pivot rule is invoked.
 **
 ** During this proccess, we periodically inspect the queue of variables to
 ** 1) remove now extraneous extries,
 ** 2) detect conflicts that are "waiting" on the queue but may not be detected by the
 **  current queue heuristics, and
 ** 3) detect multiple conflicts.
 **
 ** Conflicts are greedily slackened to use the weakest bounds that still produce the
 ** conflict.
 **
 ** Extra things tracked atm: (Subject to change at Tim's whims)
 ** - A superset of all of the newly pivoted variables.
 ** - A queue of additional conflicts that were discovered by Simplex.
 **   These are theory valid and are currently turned into lemmas
 **/


#include "cvc4_private.h"

#pragma once

#include <unordered_map>

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "theory/arith/error_set.h"
#include "theory/arith/linear_equality.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/tableau.h"
#include "util/dense_map.h"
#include "util/result.h"

namespace CVC4 {
namespace theory {
namespace arith {

class SimplexDecisionProcedure {
protected:
  typedef std::vector< std::pair<ArithVar, int> > AVIntPairVec;

  /** Pivot count of the current round of pivoting. */
  uint32_t d_pivots;

  /** The set of variables that are in conflict in this round. */
  DenseSet d_conflictVariables;

  /** The rule to use for heuristic selection mode. */
  options::ErrorSelectionRule d_heuristicRule;

  /** Linear equality module. */
  LinearEqualityModule& d_linEq;

  /**
   * Manages information about the assignment and upper and lower bounds on
   * variables.
   * Partial model matches that in LinearEqualityModule.
   */
  ArithVariables& d_variables;

  /**
   * Stores the linear equalities used by Simplex.
   * Tableau from the LinearEquality module.
   */
  Tableau& d_tableau;

  /** Contains a superset of the basic variables in violation of their bounds. */
  ErrorSet& d_errorSet;

  /** Number of variables in the system. This is used for tuning heuristics. */
  ArithVar d_numVariables;

  /** This is the call back channel for Simplex to report conflicts. */
  RaiseConflict d_conflictChannel;

  /** This is the call back channel for Simplex to report conflicts. */
  FarkasConflictBuilder* d_conflictBuilder;

  /** Used for requesting d_opt, bound and error variables for primal.*/
  TempVarMalloc d_arithVarMalloc;

  /** The size of the error set. */
  uint32_t d_errorSize;

  /** A local copy of 0. */
  const Rational d_zero;

  /** A local copy of 1. */
  const Rational d_posOne;

  /** A local copy of -1. */
  const Rational d_negOne;

  ArithVar constructInfeasiblityFunction(TimerStat& timer);
  ArithVar constructInfeasiblityFunction(TimerStat& timer, ArithVar e);
  ArithVar constructInfeasiblityFunction(TimerStat& timer, const ArithVarVec& set);

  void tearDownInfeasiblityFunction(TimerStat& timer, ArithVar inf);
  void adjustInfeasFunc(TimerStat& timer, ArithVar inf, const AVIntPairVec& focusChanges);
  void addToInfeasFunc(TimerStat& timer, ArithVar inf, ArithVar e);
  void removeFromInfeasFunc(TimerStat& timer, ArithVar inf, ArithVar e);
  void shrinkInfeasFunc(TimerStat& timer, ArithVar inf, const ArithVarVec& dropped);

public:
  SimplexDecisionProcedure(LinearEqualityModule& linEq, ErrorSet& errors, RaiseConflict conflictChannel, TempVarMalloc tvmalloc);
  virtual ~SimplexDecisionProcedure();

  /**
   * Tries to update the assignments of variables such that all of the
   * assignments are consistent with their bounds.
   * This is done by a simplex search through the possible bases of the tableau.
   *
   * If all of the variables can be made consistent with their bounds
   * SAT is returned. Otherwise UNSAT is returned, and at least 1 conflict
   * was reported on the conflictCallback passed to the Module.
   *
   * Tableau pivoting is performed so variables may switch from being basic to
   * nonbasic and vice versa.
   *
   * Corresponds to the "check()" procedure in [Cav06].
   */
  virtual Result::Sat findModel(bool exactResult) = 0;

  void increaseMax() { d_numVariables++; }


  uint32_t getPivots() const { return d_pivots; }
protected:

  /** Reports a conflict to on the output channel. */
  void reportConflict(ArithVar basic);

  /**
   * Checks a basic variable, b, to see if it is in conflict.
   * If a conflict is discovered a node summarizing the conflict is returned.
   * Otherwise, Node::null() is returned.
   */
  bool maybeGenerateConflictForBasic(ArithVar basic) const;

  /** Returns true if a tracked basic variable has a conflict on it. */
  bool checkBasicForConflict(ArithVar b) const;

  /**
   * If a basic variable has a conflict on its row,
   * this produces a minimized row on the conflict channel.
   */
  ConstraintCP generateConflictForBasic(ArithVar basic) const;


  /** Gets a fresh variable from TheoryArith. */
  ArithVar requestVariable(){
    return d_arithVarMalloc.request();
  }

  /** Releases a requested variable from TheoryArith.*/
  void releaseVariable(ArithVar v){
    d_arithVarMalloc.release(v);
  }

  /** Post condition: !d_queue.moreSignals() */
  bool standardProcessSignals(TimerStat &timer, IntStat& conflictStat);

  struct ArithVarIntPairHashFunc {
    size_t operator()(const std::pair<ArithVar, int>& p) const {
      size_t h1 = std::hash<ArithVar>()(p.first);
      size_t h2 = std::hash<int>()(p.second);
      return h1 + 3389 * h2;
    }
  };

  typedef std::unordered_map< std::pair<ArithVar, int>, ArithVarVec, ArithVarIntPairHashFunc> sgn_table;

  static inline int determinizeSgn(int sgn){
    return sgn < 0 ? -1 : (sgn == 0 ? 0 : 1);
  }

  void addSgn(sgn_table& sgns, ArithVar col, int sgn, ArithVar basic);
  void addRowSgns(sgn_table& sgns, ArithVar basic, int norm);
  ArithVar find_basic_in_sgns(const sgn_table& sgns, ArithVar col, int sgn, const DenseSet& m, bool inside);

  sgn_table::const_iterator find_sgns(const sgn_table& sgns, ArithVar col, int sgn);

};/* class SimplexDecisionProcedure */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
