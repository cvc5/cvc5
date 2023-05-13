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
 * Implements utilities for cdcac.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__CDCAC_UTILS_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__CDCAC_UTILS_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <vector>

#include "expr/node.h"
#include "theory/arith/nl/coverings/projections.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

/**
 * An interval as specified in section 4.1 of
 * https://arxiv.org/pdf/2003.05633.pdf.
 *
 * It consists of
 * - the interval id, used to map the interval to its (partial) proof,
 * - the actual interval, either an open or a point interal,
 * - the characterizing polynomials of the lower and upper bound,
 * - the characterizing polynomials in the main variable,
 * - the characterizing polynomials in lower variables and
 * - the constraints used to derive this interval.
 */
struct CACInterval
{
  /** Id of this interval to couple it to the proof */
  size_t d_id;
  /** The actual interval. */
  poly::Interval d_interval;
  /** The polynomials characterizing the lower bound. */
  PolyVector d_lowerPolys;
  /** The polynomials characterizing the upper bound. */
  PolyVector d_upperPolys;
  /** The characterizing polynomials in the main variable. */
  PolyVector d_mainPolys;
  /** The characterizing polynomials in lower variables. */
  PolyVector d_downPolys;
  /** The constraints used to derive this interval. */
  std::vector<Node> d_origins;
};
/** Check whether to intervals are the same. */
bool operator==(const CACInterval& lhs, const CACInterval& rhs);
/** Compare two intervals. */
bool operator<(const CACInterval& lhs, const CACInterval& rhs);

/**
 * Sort intervals according to section 4.4.1.
 * Also removes fully redundant intervals as in 4.5. 1.; these are intervals
 * that are fully contained within a single other interval.
 */
void cleanIntervals(std::vector<CACInterval>& intervals);

/**
 * Removes redundant intervals as in 4.5. 2.; these are intervals that are
 * covered by two other intervals, but not by a single one. Assumes the
 * intervals to be sorted and cleaned, i.e. that cleanIntervals(intervals) has
 * been called beforehand.
 */
void removeRedundantIntervals(std::vector<CACInterval>& intervals);

/**
 * Collect all origins from the list of intervals to construct the origins for a
 * whole covering.
 */
std::vector<Node> collectConstraints(const std::vector<CACInterval>& intervals);

/**
 * Sample a point outside of the infeasible intervals.
 * Stores the sample in sample, returns whether such a sample exists.
 * If false is returned, the infeasible intervals cover the real line.
 * Implements sample_outside() from section 4.3
 */
bool sampleOutside(const std::vector<CACInterval>& infeasible,
                   poly::Value& sample);

/**
 * Compute the finest square of the upper polynomials of lhs and the lower
 * polynomials of rhs. Also pushes reduced polynomials to lower level if
 * necessary.
 */
void makeFinestSquareFreeBasis(CACInterval& lhs, CACInterval& rhs);

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif

#endif
