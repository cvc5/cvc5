/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for final processing proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_FINAL_CALLBACK_H
#define CVC5__SMT__PROOF_FINAL_CALLBACK_H

#include <map>
#include <sstream>
#include <unordered_set>

#include "proof/proof_node_updater.h"
#include "rewriter/rewrites.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace smt {

/** Final callback class, for stats and pedantic checking */
class ProofFinalCallback : protected EnvObj, public ProofNodeUpdaterCallback
{
 public:
  ProofFinalCallback(Env& env);
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Should proof pn be updated? Returns false, adds to stats. */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** was pedantic failure */
  bool wasPedanticFailure(std::ostream& out) const;

 private:
  /** Counts number of postprocessed proof nodes for each kind of proof rule */
  HistogramStat<PfRule> d_ruleCount;
  /**
   * Counts number of postprocessed proof nodes of rule INSTANTIATE that were
   * marked with the given inference id.
   */
  HistogramStat<theory::InferenceId> d_instRuleIds;
  /**
   * Counts number of postprocessed proof nodes of rule ANNOTATION that were
   * marked with the given inference id.
   */
  HistogramStat<theory::InferenceId> d_annotationRuleIds;
  /** Counts number of postprocessed proof nodes for each kind of DSL proof rule
   */
  HistogramStat<rewriter::DslPfRule> d_dslRuleCount;
  /** Total number of postprocessed rule applications */
  IntStat d_totalRuleCount;
  /** The minimum pedantic level of any rule encountered */
  IntStat d_minPedanticLevel;
  /** The total number of final proofs */
  IntStat d_numFinalProofs;
  /** Was there a pedantic failure? */
  bool d_pedanticFailure;
  /** The pedantic failure string for debugging */
  std::stringstream d_pedanticFailureOut;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
