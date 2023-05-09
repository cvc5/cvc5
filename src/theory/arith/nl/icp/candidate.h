/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Represents a contraction candidate for ICP-style propagation.
 */

#ifndef CVC5__THEORY__ARITH__ICP__CANDIDATE_H
#define CVC5__THEORY__ARITH__ICP__CANDIDATE_H

#include "cvc5_private.h"

#ifdef CVC5_POLY_IMP
#include <poly/polyxx.h>

#include "expr/node.h"
#include "theory/arith/nl/icp/intersection.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

/**
 * A contraction candidate for ICP-style propagation with the following
 * semantics:
 *
 *   lhs  ~rel~  rhsmult*rhs
 *
 * where lhs is the variable whose interval we aim to contract, rel is a
 * relation symbol (other than disequality), rhsmult is a fractional constant
 * and rhs a polynomial. As poly::Polynomial only holds integer polynomials,
 * rhsmult is necessary to encode polynomials with rational coefficients.
 *
 * Additionally, we store the origin of this constraints (a single theory
 * constraint) and the variables contained in rhs.
 *
 * A candidate is evaluated (or propagated) by evaluating the rhsmult*rhs over
 * an interval assignment and then updating the interval assignment for lhs with
 * the result of this evaluation, properly considering the relation.
 */
struct Candidate
{
  /** The target variable */
  poly::Variable lhs;
  /** The relation symbol */
  poly::SignCondition rel;
  /** The (integer) polynomial on the right hand side */
  poly::Polynomial rhs;
  /** The rational multiplier */
  poly::Rational rhsmult;
  /** The origin of this candidate */
  Node origin;
  /** The variable within rhs */
  std::vector<Node> rhsVariables;

  /**
   * Contract the interval assignment based on this candidate.
   * Only contract if the new interval is below the given threshold, see
   * intersect_interval_with().
   */
  PropagationResult propagate(poly::IntervalAssignment& ia,
                              std::size_t size_threshold) const;
};

/** Print a candidate. */
std::ostream& operator<<(std::ostream& os, const Candidate& c);

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif

#endif
