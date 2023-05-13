/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for SMT engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SOLVER_ENGINE_STATS_H
#define CVC5__SMT__SOLVER_ENGINE_STATS_H

#include "util/statistics_registry.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace smt {

struct SolverEngineStatistics
{
  SolverEngineStatistics(StatisticsRegistry& sr,
                         const std::string& name = "smt::SolverEngine::");
  /** time spent in definition-expansion */
  TimerStat d_definitionExpansionTime;
  /** number of constant propagations found during nonclausal simp */
  IntStat d_numConstantProps;
  /** Number of assertions before ite removal */
  IntStat d_numAssertionsPre;
  /** Number of assertions after ite removal */
  IntStat d_numAssertionsPost;
  /** time spent in checkModel() */
  TimerStat d_checkModelTime;
  /** time spent in checkUnsatCore() */
  TimerStat d_checkUnsatCoreTime;
  /** time spent in PropEngine::checkSat() */
  TimerStat d_solveTime;
  /** time spent in pushing/popping */
  TimerStat d_pushPopTime;
  /** time spent in processAssertions() */
  TimerStat d_processAssertionsTime;

  /** Has something simplified to false? */
  IntStat d_simplifiedToFalse;
}; /* struct SolverEngineStatistics */

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__SMT_ENGINE_STATS_H */
