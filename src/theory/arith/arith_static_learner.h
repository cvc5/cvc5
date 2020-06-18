/*********************                                                        */
/*! \file arith_static_learner.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H
#define CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H

#include <set>

#include "context/cdhashmap.h"
#include "context/context.h"
#include "theory/arith/arith_utilities.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace arith {

class ArithStaticLearner {
private:

  /**
   * Map from a node to it's minimum and maximum.
   */
  typedef context::CDHashMap<Node, DeltaRational, NodeHashFunction> CDNodeToMinMaxMap;
  CDNodeToMinMaxMap d_minMap;
  CDNodeToMinMaxMap d_maxMap;

public:
  ArithStaticLearner(context::Context* userContext);
  ~ArithStaticLearner();
  void staticLearning(TNode n, NodeBuilder<>& learned);

  void addBound(TNode n);

private:
  void process(TNode n, NodeBuilder<>& learned, const TNodeSet& defTrue);

  void iteMinMax(TNode n, NodeBuilder<>& learned);
  void iteConstant(TNode n, NodeBuilder<>& learned);

  /** These fields are designed to be accessible to ArithStaticLearner methods. */
  class Statistics {
  public:
    IntStat d_iteMinMaxApplications;
    IntStat d_iteConstantApplications;

    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

};/* class ArithStaticLearner */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARITH__ARITH_STATIC_LEARNER_H */
