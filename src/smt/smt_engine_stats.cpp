/*********************                                                        */
/*! \file smt_engine_stats.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of statistics for SMT engine
 **/

#include "smt/smt_engine_stats.h"

#include "smt/smt_statistics_registry.h"

namespace cvc5 {
namespace smt {

SmtEngineStatistics::SmtEngineStatistics()
    : d_definitionExpansionTime(smtStatisticsRegistry().registerTimer(
        "smt::SmtEngine::definitionExpansionTime")),
      d_numConstantProps(smtStatisticsRegistry().registerInt(
          "smt::SmtEngine::numConstantProps")),
      d_cnfConversionTime(smtStatisticsRegistry().registerTimer(
          "smt::SmtEngine::cnfConversionTime")),
      d_numAssertionsPre(smtStatisticsRegistry().registerInt(
          "smt::SmtEngine::numAssertionsPreITERemoval")),
      d_numAssertionsPost(smtStatisticsRegistry().registerInt(
          "smt::SmtEngine::numAssertionsPostITERemoval")),
      d_checkModelTime(smtStatisticsRegistry().registerTimer(
          "smt::SmtEngine::checkModelTime")),
      d_checkUnsatCoreTime(smtStatisticsRegistry().registerTimer(
          "smt::SmtEngine::checkUnsatCoreTime")),
      d_solveTime(
          smtStatisticsRegistry().registerTimer("smt::SmtEngine::solveTime")),
      d_pushPopTime(
          smtStatisticsRegistry().registerTimer("smt::SmtEngine::pushPopTime")),
      d_processAssertionsTime(smtStatisticsRegistry().registerTimer(
          "smt::SmtEngine::processAssertionsTime")),
      d_simplifiedToFalse(smtStatisticsRegistry().registerInt(
          "smt::SmtEngine::simplifiedToFalse"))
{
}

}  // namespace smt
}  // namespace cvc5
