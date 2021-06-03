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
 * Implements utilities for cdcac.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__CAD__CDCAC_UTILS_H
#define CVC5__THEORY__ARITH__NL__CAD__CDCAC_UTILS_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <vector>

#include "expr/node.h"
#include "theory/arith/nl/cad/projections.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

/**
 * An interval as specified in section 4.1 of
 * https://arxiv.org/pdf/2003.05633.pdf.
 *
 * It consists of
 * - the actual interval, either an open or a point interal,
 * - the characterizing polynomials of the lower and upper bound,
 * - the characterizing polynomials in the main variable,
 * - the characterizing polynomials in lower variables and
 * - the constraints used to derive this interval.
 */
struct CACInterval
{
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

/** Check whether lhs covers rhs. */
bool intervalCovers(const poly::Interval& lhs, const poly::Interval& rhs);
/**
 * Check whether two intervals connect, assuming lhs < rhs.
 * They connect, if their union has no gap.
 */
bool intervalConnect(const poly::Interval& lhs, const poly::Interval& rhs);

/**
 * Sort intervals according to section 4.4.1.
 * Also removes fully redundant intervals as in 4.5. 1.
 */
void cleanIntervals(std::vector<CACInterval>& intervals);

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

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif

#endif
