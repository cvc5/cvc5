/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for post-processing proof nodes for DSL rewrite reconstruction.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_POST_PROCESSOR_DSL_H
#define CVC5__SMT__PROOF_POST_PROCESSOR_DSL_H

#include <map>
#include <sstream>
#include <unordered_set>

#include "proof/proof_node_updater.h"
#include "rewriter/rewrite_db_proof_cons.h"
#include "rewriter/rewrites.h"
#include "smt/env_obj.h"
#include "theory/smt_engine_subsolver.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace smt {

/**
 * A class for running RARE proof reconstruction for rewrite rules.
 */
class ProofPostprocessDsl : protected EnvObj, public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessDsl(Env& env, rewriter::RewriteDb* rdb);

  /**
   * Run the DSL reconstruction on each proof in pfs. This updates pfs
   * in-place based on the rewrite rule reconstruction algorithm.
   */
  void reconstruct(std::vector<std::shared_ptr<ProofNode>>& pfs);

  /** Should proof pn be updated? */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Should proof pn be updated (post-traversal)? */
  bool shouldUpdatePost(std::shared_ptr<ProofNode> pn,
                        const std::vector<Node>& fa) override;
  /** Update the proof rule application. */
  bool update(Node res,
              ProofRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** Common constants */
  Node d_true;
  /** The rewrite database proof generator */
  rewriter::RewriteDbProofCons d_rdbPc;
  /** The default mode for if/when to try theory rewrites */
  rewriter::TheoryRewriteMode d_tmode;
  /** The current proofs we are traversing */
  std::vector<std::shared_ptr<ProofNode>> d_traversing;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
