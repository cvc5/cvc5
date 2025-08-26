/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic static learner
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
  * Get proof for fact, which was a lemma constructed by this class (added
  * to the learned vector in a call to staticLearning). We expect
  * fact to be roughly one of these forms, modulo rewriting:
  *
  * 1. (<r> (ite (<r> t s) t s) t)
  * 2. (<r> (ite (<r> t s) t s) s)
  * 3. (=> (and (<r> t c) (<r> s c)) (<r> (ite C t s) c)) where c is a value.
  *
  * for some arithmetic inequality relation <r>.
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
