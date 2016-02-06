/*********************                                                        */
/*! \file smt_statistic_registry.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Accessor for the SmtEngine's StatisticsRegistry.
 **
 ** Accessor for the SmtEngine's StatisticsRegistry.
 **/


#include "smt/smt_statistics_registry.h"

#include "smt/smt_engine_scope.h"
#include "util/statistics_registry.h"

namespace CVC4 {

StatisticsRegistry* smtStatisticsRegistry() {
  return smt::SmtScope::currentStatisticsRegistry();
}

}/* CVC4 namespace */
