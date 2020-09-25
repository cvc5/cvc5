/*********************                                                        */
/*! \file bags_statistics.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS_STATISTICS_H
#define CVC4__THEORY__BAGS_STATISTICS_H

#include "expr/kind.h"
#include "theory/bags/rewrites.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace bags {

/**
 * Statistics for the theory of bags.
 */
class BagsStatistics
{
 public:
  BagsStatistics();
  ~BagsStatistics();

  /** Counts the number of applications of each type of rewrite rule */
  HistogramStat<Rewrite> d_rewrites;
};

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS_STATISTICS_H */
