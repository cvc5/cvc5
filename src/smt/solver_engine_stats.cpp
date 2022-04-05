/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of statistics for SMT engine.
 */

#include "smt/solver_engine_stats.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5::internal {
namespace smt {

SolverEngineStatistics::SolverEngineStatistics(const std::string& name)
    : d_definitionExpansionTime(smtStatisticsRegistry().registerTimer(
        name + "definitionExpansionTime")),
      d_numConstantProps(
          smtStatisticsRegistry().registerInt(name + "numConstantProps")),
      d_numAssertionsPre(smtStatisticsRegistry().registerInt(
          name + "numAssertionsPreITERemoval")),
      d_numAssertionsPost(smtStatisticsRegistry().registerInt(
          name + "numAssertionsPostITERemoval")),
      d_checkModelTime(
          smtStatisticsRegistry().registerTimer(name + "checkModelTime")),
      d_checkUnsatCoreTime(
          smtStatisticsRegistry().registerTimer(name + "checkUnsatCoreTime")),
      d_solveTime(smtStatisticsRegistry().registerTimer(name + "solveTime")),
      d_pushPopTime(
          smtStatisticsRegistry().registerTimer(name + "pushPopTime")),
      d_processAssertionsTime(smtStatisticsRegistry().registerTimer(
          name + "processAssertionsTime")),
      d_simplifiedToFalse(
          smtStatisticsRegistry().registerInt(name + "simplifiedToFalse"))
{
}

}  // namespace smt
}  // namespace cvc5::internal
