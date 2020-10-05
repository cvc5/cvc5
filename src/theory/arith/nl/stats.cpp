/*********************                                                        */
/*! \file stats.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for non-linear arithmetic
 **/

#include "theory/arith/nl/stats.h"

#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

NlStats::NlStats()
    : d_mbrRuns("nl::mbrRuns", 0),
      d_checkRuns("nl::checkRuns", 0),
      d_inferences("nl::inferences")
{
  smtStatisticsRegistry()->registerStat(&d_mbrRuns);
  smtStatisticsRegistry()->registerStat(&d_checkRuns);
  smtStatisticsRegistry()->registerStat(&d_inferences);
}

NlStats::~NlStats()
{
  smtStatisticsRegistry()->unregisterStat(&d_mbrRuns);
  smtStatisticsRegistry()->unregisterStat(&d_checkRuns);
  smtStatisticsRegistry()->unregisterStat(&d_inferences);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
