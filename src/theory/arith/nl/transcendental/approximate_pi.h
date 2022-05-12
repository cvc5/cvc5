/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Incremental approximation scheme for pi.
 */

#ifndef CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__APPROXIMATE_PI_H
#define CVC5__THEORY__ARITH__NL__TRANSCENDENTAL__APPROXIMATE_PI_H

#include "expr/node_manager.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5 {
namespace internal {
namespace theory {
namespace arith {
namespace nl {
namespace transcendental {

/**
 * Utility to incrementally approximate pi and provide safe lower and upper
 * bounds. The implementation is based on the Bailey-Borwein-Plouffe formula
 * in the following formulation:
 *             (  1            120k^2 + 151k + 47             )
 * pi = \sum_k ( ---- * ------------------------------------- )
 *             ( 16^k   512k^4 + 1025k^3 + 712k^2 + 194k + 15 )
 *
 * Every summand (except for k=0) is between zero and 1/16^k. Thus:
 * - adding one summand improves the approximation by 4 correct bits
 * - every partial sum is a proper lower bound
 * - every partial sum (k>0) plus 1/16^k is a proper upper bound
 *
 * Furthermore, the rate of convergenve is comparably slow, making sure that we
 * do not end up with huge constants / coefficients immediately.
 */
class ApproximatePi
{
 public:
  ApproximatePi();
  const Rational& getLower() const { return d_lower; }
  const Rational& getUpper() const { return d_upper; }
  Node getLowerNode() const
  {
    return NodeManager::currentNM()->mkConstReal(d_lower);
  }
  Node getUpperNode() const
  {
    return NodeManager::currentNM()->mkConstReal(d_upper);
  }
  void refine();

 private:
  Rational d_lower;
  Rational d_upper;
  uint32_t d_next_k = 0;
  static constexpr uint32_t s_initial_refinement = 1;
}; /* class ApproximatePi */

}  // namespace transcendental
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace internal
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__TRANSCENDENTAL_SOLVER_H */
