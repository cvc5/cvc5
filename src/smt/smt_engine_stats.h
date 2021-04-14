/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for SMT engine.
 */

#include "cvc4_private.h"

#ifndef CVC5__SMT__SMT_ENGINE_STATS_H
#define CVC5__SMT__SMT_ENGINE_STATS_H

#include "util/statistics_registry.h"
#include "util/stats_timer.h"

namespace cvc5 {
namespace smt {

struct SmtEngineStatistics
{
  SmtEngineStatistics();
  ~SmtEngineStatistics();
  /** time spent in definition-expansion */
  TimerStat d_definitionExpansionTime;
  /** number of constant propagations found during nonclausal simp */
  IntStat d_numConstantProps;
  /** time spent converting to CNF */
  TimerStat d_cnfConversionTime;
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

  /** Name of the input file */
  BackedStat<std::string> d_driverFilename;
  /** Result of the last check */
  BackedStat<std::string> d_driverResult;
  /** Total time of the current run */
  BackedStat<double> d_driverTotalTime;
}; /* struct SmtEngineStatistics */

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__SMT_ENGINE_STATS_H */
