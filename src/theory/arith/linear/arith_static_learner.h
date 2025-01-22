/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/delta_rational.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class ArithStaticLearner : protected EnvObj, public ProofGenerator
{
 private:

  /**
   * Map from a node to it's minimum and maximum.
   */
 typedef context::CDHashMap<Node, DeltaRational> CDNodeToMinMaxMap;
 CDNodeToMinMaxMap d_minMap;
 CDNodeToMinMaxMap d_maxMap;

public:
 ArithStaticLearner(Env& env);
 ~ArithStaticLearner();
 void staticLearning(TNode n, std::vector<TrustNode>& learned);

 void addBound(TNode n);
 /**
  * Get proof for fact
  */
 std::shared_ptr<ProofNode> getProofFor(Node fact) override;
 /** identify this proof generator */
 std::string identify() const override;

private:
 void process(TNode n,
              std::vector<TrustNode>& learned,
              const TNodeSet& defTrue);

 void iteMinMax(TNode n, std::vector<TrustNode>& learned);
 void iteConstant(TNode n, std::vector<TrustNode>& learned);
 /** Add learned lemma n to learned, no proofs currently */
 void addLearnedLemma(TNode n, std::vector<TrustNode>& learned);

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

}; /* class ArithStaticLearner */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_STATIC_LEARNER_H */
