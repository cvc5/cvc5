/*********************                                                        */
/*! \file smt_engine_stats.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for SMT engine
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__SMT_ENGINE_STATS_H
#define CVC4__SMT__SMT_ENGINE_STATS_H

#include "util/statistics_registry.h"

namespace CVC4 {
namespace smt {

struct SmtEngineStatistics {
  /** time spent in definition-expansion */
  TimerStat d_definitionExpansionTime;
  /** number of constant propagations found during nonclausal simp */
  IntStat d_numConstantProps;
  /** time spent converting to CNF */
  TimerStat d_cnfConversionTime;
  /** Num of assertions before ite removal */
  IntStat d_numAssertionsPre;
  /** Num of assertions after ite removal */
  IntStat d_numAssertionsPost;
  /** Size of all proofs generated */
  IntStat d_proofsSize;
  /** time spent in checkModel() */
  TimerStat d_checkModelTime;
  /** time spent checking the proof with LFSC */
  TimerStat d_lfscCheckProofTime;
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
  /** Number of resource units spent. */
  ReferenceStat<uint64_t> d_resourceUnitsUsed;

  SmtEngineStatistics()
      : d_definitionExpansionTime("smt::SmtEngine::definitionExpansionTime"),
        d_numConstantProps("smt::SmtEngine::numConstantProps", 0),
        d_cnfConversionTime("smt::SmtEngine::cnfConversionTime"),
        d_numAssertionsPre("smt::SmtEngine::numAssertionsPreITERemoval", 0),
        d_numAssertionsPost("smt::SmtEngine::numAssertionsPostITERemoval", 0),
        d_proofsSize("smt::SmtEngine::proofsSize", 0),
        d_checkModelTime("smt::SmtEngine::checkModelTime"),
        d_lfscCheckProofTime("smt::SmtEngine::lfscCheckProofTime"),
        d_checkUnsatCoreTime("smt::SmtEngine::checkUnsatCoreTime"),
        d_solveTime("smt::SmtEngine::solveTime"),
        d_pushPopTime("smt::SmtEngine::pushPopTime"),
        d_processAssertionsTime("smt::SmtEngine::processAssertionsTime"),
        d_simplifiedToFalse("smt::SmtEngine::simplifiedToFalse", 0),
        d_resourceUnitsUsed("smt::SmtEngine::resourceUnitsUsed")
  {
    smtStatisticsRegistry()->registerStat(&d_definitionExpansionTime);
    smtStatisticsRegistry()->registerStat(&d_numConstantProps);
    smtStatisticsRegistry()->registerStat(&d_cnfConversionTime);
    smtStatisticsRegistry()->registerStat(&d_numAssertionsPre);
    smtStatisticsRegistry()->registerStat(&d_numAssertionsPost);
    smtStatisticsRegistry()->registerStat(&d_proofsSize);
    smtStatisticsRegistry()->registerStat(&d_checkModelTime);
    smtStatisticsRegistry()->registerStat(&d_lfscCheckProofTime);
    smtStatisticsRegistry()->registerStat(&d_checkUnsatCoreTime);
    smtStatisticsRegistry()->registerStat(&d_solveTime);
    smtStatisticsRegistry()->registerStat(&d_pushPopTime);
    smtStatisticsRegistry()->registerStat(&d_processAssertionsTime);
    smtStatisticsRegistry()->registerStat(&d_simplifiedToFalse);
    smtStatisticsRegistry()->registerStat(&d_resourceUnitsUsed);
  }

  ~SmtEngineStatistics() {
    smtStatisticsRegistry()->unregisterStat(&d_definitionExpansionTime);
    smtStatisticsRegistry()->unregisterStat(&d_numConstantProps);
    smtStatisticsRegistry()->unregisterStat(&d_cnfConversionTime);
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPre);
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPost);
    smtStatisticsRegistry()->unregisterStat(&d_proofsSize);
    smtStatisticsRegistry()->unregisterStat(&d_checkModelTime);
    smtStatisticsRegistry()->unregisterStat(&d_lfscCheckProofTime);
    smtStatisticsRegistry()->unregisterStat(&d_checkUnsatCoreTime);
    smtStatisticsRegistry()->unregisterStat(&d_solveTime);
    smtStatisticsRegistry()->unregisterStat(&d_pushPopTime);
    smtStatisticsRegistry()->unregisterStat(&d_processAssertionsTime);
    smtStatisticsRegistry()->unregisterStat(&d_simplifiedToFalse);
    smtStatisticsRegistry()->unregisterStat(&d_resourceUnitsUsed);
  }
};/* struct SmtEngineStatistics */

}
}

#endif /* CVC4__SMT__SMT_ENGINE_STATS_H */
