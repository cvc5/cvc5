/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the theory of bags.
 */

#include "theory/bags/bags_statistics.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

BagsStatistics::BagsStatistics(StatisticsRegistry& sr)
    : d_rewrites(sr.registerHistogram<Rewrite>("theory::bags::rewrites"))
{
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
