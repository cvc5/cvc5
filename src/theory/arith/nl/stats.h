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
#include "theory/arith/inference_id.h"
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
  /**
   * Number of calls to NonlinearExtension::modelBasedRefinement. Notice this
   * may make multiple calls to NonlinearExtension::checkLastCall.
   */
  IntStat d_mbrRuns;
  /** Number of calls to NonlinearExtension::checkLastCall */
  IntStat d_checkRuns;
  /** Counts the number of applications of each type of inference */
  HistogramStat<InferenceId> d_inferences;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL__STATS_H */
