/*********************                                                        */
/*! \file smt_engine_stats.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for SMT engine
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__SMT_ENGINE_STATS_H
#define CVC4__SMT__SMT_ENGINE_STATS_H

#include "util/statistics_stats.h"

namespace CVC4 {
namespace smt {

struct SmtEngineStatistics
{
  SmtEngineStatistics();
  /** time spent in definition-expansion */
  TimerStats d_definitionExpansionTime;
  /** number of constant propagations found during nonclausal simp */
  IntStats d_numConstantProps;
  /** time spent converting to CNF */
  TimerStats d_cnfConversionTime;
  /** Number of assertions before ite removal */
  IntStats d_numAssertionsPre;
  /** Number of assertions after ite removal */
  IntStats d_numAssertionsPost;
  /** time spent in checkModel() */
  TimerStats d_checkModelTime;
  /** time spent in checkUnsatCore() */
  TimerStats d_checkUnsatCoreTime;
  /** time spent in PropEngine::checkSat() */
  TimerStats d_solveTime;
  /** time spent in pushing/popping */
  TimerStats d_pushPopTime;
  /** time spent in processAssertions() */
  TimerStats d_processAssertionsTime;

  /** Has something simplified to false? */
  IntStats d_simplifiedToFalse;

  TimerStats d_totalTime;
}; /* struct SmtEngineStatistics */

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__SMT_ENGINE_STATS_H */
