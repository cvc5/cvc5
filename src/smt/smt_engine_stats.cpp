/*********************                                                        */
/*! \file smt_engine_stats.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of statistics for SMT engine
 **/

#include "smt/smt_engine_stats.h"

#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace smt {

SmtEngineStatistics::SmtEngineStatistics()
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
      d_simplifiedToFalse("smt::SmtEngine::simplifiedToFalse", 0)
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
}

SmtEngineStatistics::~SmtEngineStatistics()
{
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
}

}  // namespace smt
}  // namespace CVC4
