/*********************                                                        */
/*! \file smt_statistics_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
