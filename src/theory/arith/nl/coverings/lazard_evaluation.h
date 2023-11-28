/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Alex Ozdemir, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements the CDCAC approach as described in
 * https://arxiv.org/pdf/2003.05633.pdf.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__LAZARD_EVALUATION_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__LAZARD_EVALUATION_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <memory>

#include "util/statistics_stats.h"

namespace cvc5::internal::theory::arith::nl::coverings {

struct LazardEvaluationStats
{
  IntStat d_directAssignments;
  IntStat d_ranAssignments;
  IntStat d_evaluations;
  IntStat d_reductions;
  LazardEvaluationStats(StatisticsRegistry& reg);
};

struct LazardEvaluationState;
/**
 * This class does the heavy lifting for the modified lifting procedure that is
 * required for Lazard's projection.
 *
 * Let p \in Q[x_0, ..., x_n] a multivariate polynomial whose roots we want to
 * isolate over the partial sample point A = [x_0 = a_0, ... x_{n-1} = a_{n-1}]
 * where a_0, ... a_{n-1} are real algebraic numbers and x_n is the last free
 * variable.
 *
 * The modified lifting procedure conceptually works as follows:
 *
 * for (x = a) in A:
 *    while p[x // a] = 0:
 *       p = p / (x - a)
 *    p = p[x // a]
 * return roots(p)
 *
 * As the assignment contains real algebraic numbers, though, we can not do any
 * of the computations directly, as our polynomials only support coefficients
 * from Z or Q, but not extensions (in the algebraic sense) thereof.
 *
 * Our approach is as follows:
 * Let pk be the minimal polynomial for a_k.
 * Instead of substituting p[x_k // a_k] we (canonically) embed p into the
 * quotient ring Q[x_k]/<p_k> and recursively build a tower of such quotient
 * rings that is isomorphic to nesting the corresponding field extensions
 * Q(a_1)(a_2)... When we have done that, we obtain p that is reduced with
 * respect to all minimal polynomials, but may still contain x_0,... x_{n-1}. To
 * get rid of these, we compute a Gröbner basis of p and the minimal polynomials
 * (using a suitable elimination order) and extract the polynomial in x_n. This
 * polynomial has all roots (and possibly some more) that we are looking for.
 * Instead of a Gröbner basis, we can also compute the iterated resultant as
 * follows: Res(Res(p, p_{n-1}, x_{n-1}), p_{n-2}, x_{n-2})...
 *
 * Consider
 * http://sunsite.informatik.rwth-aachen.de/Publications/AIB/2020/2020-04.pdf
 * Section 2.5.1 for a full discussion.
 *
 * !!! WARNING !!!
 * If CoCoALib is not available, this class will simply fall back to
 * poly::infeasible_regions and issue a warning about this.
 */
class LazardEvaluation
{
 public:
  LazardEvaluation(StatisticsRegistry& reg);
  ~LazardEvaluation();

  /**
   * Add the next assigned variable x_k = a_k to this construction.
   */
  void add(const poly::Variable& var, const poly::Value& val);
  /**
   * Finish by adding the free variable x_n.
   */
  void addFreeVariable(const poly::Variable& var);
  /**
   * Reduce the polynomial q. Compared to the above description, there may
   * actually be multiple polynomials in the Gröbner basis and instead of
   * loosing this knowledge and returning their product, we return them as a
   * vector.
   */
  std::vector<poly::Polynomial> reducePolynomial(
      const poly::Polynomial& q) const;

  /**
   * Isolates the real roots of the given polynomials.
   */
  std::vector<poly::Value> isolateRealRoots(const poly::Polynomial& q) const;

  /**
   * Compute the infeasible regions of q under the given sign condition.
   * Uses reducePolynomial and then performs real root isolation on the
   * resulting polynomials to obtain the intervals. Mimics
   * poly::infeasible_regions, but uses Lazard's evaluation.
   */
  std::vector<poly::Interval> infeasibleRegions(const poly::Polynomial& q,
                                                poly::SignCondition sc) const;

 private:
  std::unique_ptr<LazardEvaluationState> d_state;
};

}  // namespace cvc5::internal::theory::arith::nl::coverings

#endif
#endif
