/******************************************************************************
 * Top contributors (to current version):
 *   Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Accessor for the SmtEngine's StatisticsRegistry.
 */

#include "smt/smt_statistics_registry.h"

#include "smt/smt_engine_scope.h"
#include "util/statistics_stats.h"

namespace cvc5 {

StatisticsRegistry& smtStatisticsRegistry()
{
  return smt::SmtScope::currentStatisticsRegistry();
}

}  // namespace cvc5
