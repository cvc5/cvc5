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
 * Implement intersection of intervals for propagation.
 */

#ifndef CVC5__THEORY__ARITH__ICP__INTERSECTION_H
#define CVC5__THEORY__ARITH__ICP__INTERSECTION_H

#include "cvc5_private.h"

#ifdef CVC5_POLY_IMP

#include <cstddef>

namespace poly {
  class Interval;
}

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

/**
 * Represents the possible results of a single propagation step.
 * A propagation tries to refine a current interval with a new interval by
 * intersecting them.
 */
enum class PropagationResult
{
  /** The propagation did not change the current interval. */
  NOT_CHANGED,
  /** The propagation contracted the current interval. */
  CONTRACTED,
  /**
   * The propagation contracted the current interval made at least one bound
   * finite.
   */
  CONTRACTED_STRONGLY,
  /**
   * The propagation only used the new interval (as it was a subset of the
   * current interval).
   */
  CONTRACTED_WITHOUT_CURRENT,
  /**
   * The propagation only used the new interval (as it was a subset of the
   * current interval) and made at least one bound finite.
   */
  CONTRACTED_STRONGLY_WITHOUT_CURRENT,
  /**
   * The propagation found a conflict as the two intervals did not intersect.
   */
  CONFLICT
};

/**
 * Update the current interval by intersection with the new interval and return
 * the appropriate result. If the size of any of the bounds, as computed by
 * bitsize(), would grow beyond the given threshold, no intersection is
 * performed and PropagationResult::NOT_CHANGED is returned.
 */
PropagationResult intersect_interval_with(poly::Interval& cur,
                                          const poly::Interval& res,
                                          std::size_t size_threshold);

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif

#endif
