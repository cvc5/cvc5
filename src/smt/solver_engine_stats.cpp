/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

SolverEngineStatistics::SolverEngineStatistics(StatisticsRegistry& sr,
                                               const std::string& name)
    : d_definitionExpansionTime(
        sr.registerTimer(name + "definitionExpansionTime")),
      d_numConstantProps(sr.registerInt(name + "numConstantProps")),
      d_numAssertionsPre(sr.registerInt(name + "numAssertionsPreITERemoval")),
      d_numAssertionsPost(sr.registerInt(name + "numAssertionsPostITERemoval")),
      d_checkModelTime(sr.registerTimer(name + "checkModelTime")),
      d_checkUnsatCoreTime(sr.registerTimer(name + "checkUnsatCoreTime")),
      d_solveTime(sr.registerTimer(name + "solveTime")),
      d_pushPopTime(sr.registerTimer(name + "pushPopTime")),
      d_processAssertionsTime(sr.registerTimer(name + "processAssertionsTime")),
      d_simplifiedToFalse(sr.registerInt(name + "simplifiedToFalse"))
{
}

}  // namespace smt
}  // namespace cvc5::internal
