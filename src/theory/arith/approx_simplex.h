/*********************                                                        */
/*! \file approx_simplex.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

#include "theory/arith/arithvar.h"
#include "theory/arith/delta_rational.h"
#include "util/dense_map.h"
#include "util/rational.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {

enum LinResult {
  LinUnknown,  /* Unknown error */
  LinFeasible, /* Relaxation is feasible */
  LinInfeasible,   /* Relaxation is infeasible/all integer branches closed */
  LinExhausted
};

enum MipResult {
  MipUnknown,  /* Unknown error */
  MipBingo,    /* Integer feasible */
  MipClosed,   /* All integer branches closed */
  BranchesExhausted, /* Exhausted number of branches */
  PivotsExhauasted,  /* Exhausted number of pivots */
  ExecExhausted      /* Exhausted total operations */
};
std::ostream& operator<<(std::ostream& out, MipResult res);

class ApproximateStatistics {
public:
  // IntStat d_relaxCalls;
  // IntStat d_relaxUnknowns;
  // IntStat d_relaxFeasible;
  // IntStat d_relaxInfeasible;
  // IntStat d_relaxPivotsExhausted;

  // IntStat d_mipCalls;
  // IntStat d_mipUnknowns;
  // IntStat d_mipBingo;
  // IntStat d_mipClosed;
  // IntStat d_mipBranchesExhausted;
  // IntStat d_mipPivotsExhausted;
  // IntStat d_mipExecExhausted;


  // IntStat d_gmiGen;
  // IntStat d_gmiReplay;
  // IntStat d_mipGen;
  // IntStat d_mipReplay;

  IntStat d_branchMaxDepth;
  IntStat d_branchesMaxOnAVar;

  TimerStat d_gaussianElimConstructTime;
  IntStat d_gaussianElimConstruct;
  AverageStat d_averageGuesses;

  ApproximateStatistics();
  ~ApproximateStatistics();
};


class NodeLog;
class TreeLog;
class ArithVariables;
class CutInfo;
class RowsDeleted;

class ApproximateSimplex{
protected:
  const ArithVariables& d_vars;
  TreeLog& d_log;
  ApproximateStatistics& d_stats;

  int d_pivotLimit;
  /* the maximum pivots allowed in a query. */

  int d_branchLimit;
  /* maximum branches allowed on a variable */

  int d_maxDepth;
  /* maxmimum branching depth allowed.*/

  static Integer s_defaultMaxDenom;
  /* Default denominator for diophatine approximation.
  * 2^{26}*/

public:

  static bool enabled();

  /**
   * If glpk is enabled, return a subclass that can do something.
   * If glpk is disabled, return a subclass that does nothing.
   */
  static ApproximateSimplex* mkApproximateSimplexSolver(const ArithVariables& vars, TreeLog& l, ApproximateStatistics& s);
  ApproximateSimplex(const ArithVariables& v, TreeLog& l, ApproximateStatistics& s);
  virtual ~ApproximateSimplex(){}

  /* the maximum pivots allowed in a query. */
  void setPivotLimit(int pl);

  /* maximum branches allowed on a variable */
  void setBranchOnVariableLimit(int bl);

  /* maximum branches allowed on a variable */
  void setBranchingDepth(int bd);

  /** A result is either sat, unsat or unknown.*/
  //enum ApproxResult {ApproxError, ApproxSat, ApproxUnsat};
  struct Solution {
    DenseSet newBasis;
    DenseMap<DeltaRational> newValues;
    Solution() : newBasis(), newValues(){}
  };

  virtual ArithVar getBranchVar(const NodeLog& nl) const = 0;
  //virtual void mapRowId(int nid, int ind, ArithVar v) = 0;
  //virtual void applyRowsDeleted(int nid, const RowsDeleted& rd) = 0;

  /** Sets a maximization criteria for the approximate solver.*/
  virtual void setOptCoeffs(const ArithRatPairVec& ref) = 0;

  virtual ArithRatPairVec heuristicOptCoeffs() const = 0;

  virtual LinResult solveRelaxation() = 0;
  virtual Solution extractRelaxation() const throw(RationalFromDoubleException) = 0;

  virtual MipResult solveMIP(bool activelyLog) = 0;
  virtual Solution extractMIP() const throw(RationalFromDoubleException) = 0;

  virtual std::vector<const CutInfo*> getValidCuts(const NodeLog& node) throw(RationalFromDoubleException) = 0;
  //virtual std::vector<const NodeLog*> getBranches() = 0;

  //virtual Node downBranchLiteral(const NodeLog& con) const = 0;

  virtual void tryCut(int nid, CutInfo& cut) throw(RationalFromDoubleException) = 0;

  /** UTILITIES FOR DEALING WITH ESTIMATES */

  static const double SMALL_FIXED_DELTA;
  static const double TOLERENCE;

  /** Returns true if two doubles are roughly equal based on TOLERENCE and SMALL_FIXED_DELTA.*/
  static bool roughlyEqual(double a, double b);

  /**
   * Estimates a double as a Rational using continued fraction expansion that
   * cuts off the estimate once the value is approximately zero.
   * This is designed for removing rounding artifacts.
   */
  static Rational estimateWithCFE(double d) throw(RationalFromDoubleException);
  static Rational estimateWithCFE(double d, const Integer& D) throw(RationalFromDoubleException);

  /**
   * Converts a rational to a continued fraction expansion representation
   * using a maximum number of expansions equal to depth as long as the expression
   * is not roughlyEqual() to 0.
   */
  static std::vector<Integer> rationalToCfe(const Rational& q, int depth);

  /** Converts a continued fraction expansion representation to a rational. */
  static Rational cfeToRational(const std::vector<Integer>& exp);

  /** Estimates a rational as a continued fraction expansion.*/
  //static Rational estimateWithCFE(const Rational& q, int depth);
  static Rational estimateWithCFE(const Rational& q, const Integer& K);

  virtual double sumInfeasibilities(bool mip) const = 0;
};/* class ApproximateSimplex */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
