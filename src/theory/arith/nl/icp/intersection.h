/*********************                                                        */
/*! \file intersection.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implement intersection of intervals for propagation.
 **/

#ifndef CVC4__THEORY__ARITH__ICP__INTERSECTION_H
#define CVC4__THEORY__ARITH__ICP__INTERSECTION_H

#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP
#include <poly/polyxx.h>

namespace CVC4 {
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
}  // namespace CVC4

#endif

#endif
