/*********************                                                        */
/*! \file cdcac_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements utilities for cdcac.
 **
 ** Implements utilities for cdcac.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__NL__CAD__CDCAC_UTILS_H
#define CVC4__THEORY__ARITH__NL__CAD__CDCAC_UTILS_H

#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP

#include <poly/polyxx.h>

#include <vector>

#include "expr/node.h"

namespace CVC4 {
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
  std::vector<poly::Polynomial> d_lowerPolys;
  /** The polynomials characterizing the upper bound. */
  std::vector<poly::Polynomial> d_upperPolys;
  /** The characterizing polynomials in the main variable. */
  std::vector<poly::Polynomial> d_mainPolys;
  /** The characterizing polynomials in lower variables. */
  std::vector<poly::Polynomial> d_downPolys;
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

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif

#endif
