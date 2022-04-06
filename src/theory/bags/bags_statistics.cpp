/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the theory of bags.
 */

#include "theory/bags/bags_statistics.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

BagsStatistics::BagsStatistics()
    : d_rewrites(smtStatisticsRegistry().registerHistogram<Rewrite>(
        "theory::bags::rewrites"))
{
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
