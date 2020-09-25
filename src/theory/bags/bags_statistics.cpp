/*********************                                                        */
/*! \file bags_statistics.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for the theory of bags
 **/

#include "theory/bags/bags_statistics.h"

#include "smt/smt_statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace bags {

BagsStatistics::BagsStatistics() : d_rewrites("theory::bags::rewrites")
{
  smtStatisticsRegistry()->registerStat(&d_rewrites);
}

BagsStatistics::~BagsStatistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_rewrites);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
