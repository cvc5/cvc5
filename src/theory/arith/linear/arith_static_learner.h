/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_STATIC_LEARNER_H
#define CVC5__THEORY__ARITH__ARITH_STATIC_LEARNER_H

#include "context/cdhashmap.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "util/statistics_stats.h"

namespace cvc5::context {
class Context;
}

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class ArithStaticLearner {
private:

  /**
   * Map from a node to it's minimum and maximum.
   */
 typedef context::CDHashMap<Node, DeltaRational> CDNodeToMinMaxMap;
 CDNodeToMinMaxMap d_minMap;
 CDNodeToMinMaxMap d_maxMap;

public:
 ArithStaticLearner(StatisticsRegistry& sr, context::Context* userContext);
 ~ArithStaticLearner();
 void staticLearning(TNode n, NodeBuilder& learned);

 void addBound(TNode n);

private:
 void process(TNode n, NodeBuilder& learned, const TNodeSet& defTrue);

 void iteMinMax(TNode n, NodeBuilder& learned);
 void iteConstant(TNode n, NodeBuilder& learned);

 /**
  * These fields are designed to be accessible to ArithStaticLearner methods.
  */
 class Statistics
 {
  public:
   IntStat d_iteMinMaxApplications;
   IntStat d_iteConstantApplications;

   Statistics(StatisticsRegistry& sr);
 };

  Statistics d_statistics;

};/* class ArithStaticLearner */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_STATIC_LEARNER_H */
