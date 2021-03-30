/*********************                                                        */
/*! \file justify_stats.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification stats
 **/

#include "cvc4_private.h"

#ifndef CVC4__DECISION__JUSTIFY_STATS_H
#define CVC4__DECISION__JUSTIFY_STATS_H

#include "util/statistics_registry.h"

namespace CVC4 {

class JustifyStatistics
{
 public:
  JustifyStatistics();
  ~JustifyStatistics();
  IntStat d_numStatusNoDecision;
  IntStat d_numStatusDecision;
  IntStat d_numStatusBacktrack;
  IntStat d_maxStackSize;
  IntStat d_maxAssertionsSize;
  IntStat d_maxSkolemDefsSize;
};

}  // namespace CVC4

#endif /* CVC4__DECISION__JUSTIFY_STATS_H */
