/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of statistics for SMT engine.
 */

#include "smt/solver_engine_stats.h"

namespace cvc5::internal {
namespace smt {

SolverEngineStatistics::SolverEngineStatistics(const std::string& name)
    : d_definitionExpansionTime(
        statisticsRegistry().registerTimer(name + "definitionExpansionTime")),
      d_numConstantProps(
          statisticsRegistry().registerInt(name + "numConstantProps")),
      d_numAssertionsPre(statisticsRegistry().registerInt(
          name + "numAssertionsPreITERemoval")),
      d_numAssertionsPost(statisticsRegistry().registerInt(
          name + "numAssertionsPostITERemoval")),
      d_checkModelTime(
          statisticsRegistry().registerTimer(name + "checkModelTime")),
      d_checkUnsatCoreTime(
          statisticsRegistry().registerTimer(name + "checkUnsatCoreTime")),
      d_solveTime(statisticsRegistry().registerTimer(name + "solveTime")),
      d_pushPopTime(statisticsRegistry().registerTimer(name + "pushPopTime")),
      d_processAssertionsTime(
          statisticsRegistry().registerTimer(name + "processAssertionsTime")),
      d_simplifiedToFalse(
          statisticsRegistry().registerInt(name + "simplifiedToFalse"))
{
}

}  // namespace smt
}  // namespace cvc5::internal
