
#include "cvc4_private.h"

#pragma once

#include "util/statistics_registry.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/linear_equality.h"
#include "util/dense_map.h"
#include <vector>

namespace CVC4 {
namespace theory {
namespace arith {


class ApproximateSimplex{
protected:
  int d_pivotLimit;

public:

  static bool enabled();

  /**
   * If glpk is enabled, return a subclass that can do something.
   * If glpk is disabled, return a sublass that does nothing.
   */
  static ApproximateSimplex* mkApproximateSimplexSolver(const ArithVariables& vars);
  ApproximateSimplex();
  virtual ~ApproximateSimplex(){}

  /** A result is either sat, unsat or unknown.*/
  enum ApproxResult {ApproxError, ApproxSat, ApproxUnsat};
  struct Solution {
    DenseSet newBasis;
    DenseMap<DeltaRational> newValues;
    Solution() : newBasis(), newValues(){}
  };

  /** Sets a deterministic effort limit. */
  void setPivotLimit(int pivotLimit);

  /** Sets a maximization criteria for the approximate solver.*/
  virtual void setOptCoeffs(const ArithRatPairVec& ref) = 0;

  virtual ApproxResult solveRelaxation() = 0;
  virtual Solution extractRelaxation() const = 0;

  virtual ApproxResult solveMIP() = 0;
  virtual Solution extractMIP() const = 0;

  static void applySolution(LinearEqualityModule& linEq, const Solution& sol){
    linEq.forceNewBasis(sol.newBasis);
    linEq.updateMany(sol.newValues);
  }

  /** UTILIES FOR DEALING WITH ESTIMATES */

  static const double SMALL_FIXED_DELTA;
  static const double TOLERENCE;

  /** Returns true if two doubles are roughly equal based on TOLERENCE and SMALL_FIXED_DELTA.*/
  static bool roughlyEqual(double a, double b);

  /**
   * Estimates a double as a Rational using continued fraction expansion that
   * cuts off the estimate once the value is approximately zero.
   * This is designed for removing rounding artifacts.
   */
  static Rational estimateWithCFE(double d);

  /**
   * Converts a rational to a continued fraction expansion representation
   * using a maximum number of expansions equal to depth as long as the expression
   * is not roughlyEqual() to 0.
   */
  static std::vector<Integer> rationalToCfe(const Rational& q, int depth);

  /** Converts a continued fraction expansion representation to a rational. */
  static Rational cfeToRational(const std::vector<Integer>& exp);

  /** Estimates a rational as a continued fraction expansion.*/
  static Rational estimateWithCFE(const Rational& q, int depth);
};/* class ApproximateSimplex */


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
