/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the theory of bags.
 */

#include "cvc4_private.h"

#ifndef CVC5__THEORY__BAGS_STATISTICS_H
#define CVC5__THEORY__BAGS_STATISTICS_H

#include "theory/bags/rewrites.h"
#include "util/statistics_registry.h"
#include "util/stats_histogram.h"

namespace cvc5 {
namespace theory {
namespace bags {

/**
 * Statistics for the theory of bags.
 */
class BagsStatistics
{
 public:
  BagsStatistics();
  ~BagsStatistics();

  /** Counts the number of applications of each type of rewrite rule */
  IntegralHistogramStat<Rewrite> d_rewrites;
};

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BAGS_STATISTICS_H */
