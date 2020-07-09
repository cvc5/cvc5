/*********************                                                        */
/*! \file stats.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Statistics for non-linear arithmetic
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__NL__STATS_H
#define CVC4__THEORY__ARITH__NL__STATS_H

#include "expr/kind.h"
#include "theory/arith/nl/inference.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

/**
 * Statistics for non-linear arithmetic
 */
class NlStats
{
 public:
  NlStats();
  ~NlStats();
  /** Number of calls to run a check where strategy is present */
  IntStat d_checkRuns;
  /** Counts the number of applications of each type of inference */
  HistogramStat<Inference> d_inferences;
  /**
   * Counts the number of applications of each type of context-dependent
   * simplification. The sum of this map is equal to the number of EXTF or
   * EXTF_N inferences.
   */
  HistogramStat<Kind> d_cdSimplifications;
};

}
}
}
}

#endif /* CVC4__THEORY__ARITH__NL__STATS_H */
