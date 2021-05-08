/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for non-linear arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__STATS_H
#define CVC5__THEORY__ARITH__NL__STATS_H

#include "util/statistics_stats.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

/**
 * Statistics for non-linear arithmetic
 */
class NlStats
{
 public:
  NlStats();
  /**
   * Number of calls to NonlinearExtension::modelBasedRefinement. Notice this
   * may make multiple calls to NonlinearExtension::checkLastCall.
   */
  IntStat d_mbrRuns;
  /** Number of calls to NonlinearExtension::checkLastCall */
  IntStat d_checkRuns;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__NL__STATS_H */
