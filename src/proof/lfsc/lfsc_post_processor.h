/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into Lfsc proof nodes
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_POST_PROCESSOR_H
#define CVC4__PROOF__LFSC__LFSC_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "proof/lfsc/lfsc_node_converter.h"
#include "proof/lfsc/lfsc_util.h"
#include "proof/proof_node_updater.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofChecker;

namespace proof {

/**
 * A callback class used by the Lfsc convereter for post-processing proof nodes
 * by replacing internal rules by the rules in the Lfsc calculus.
 */
class LfscProofPostprocessCallback : protected EnvObj,
                                     public ProofNodeUpdaterCallback
{
 public:
  LfscProofPostprocessCallback(Env& env, LfscNodeConverter& ltp);
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Should update */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Update the proof rule application. */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** The proof checker of d_pnm **/
  ProofChecker* d_pc;
  /** The term processor */
  LfscNodeConverter& d_tproc;
  /**
   * Are we in the first 2 calls to update? This is to distinguish the top-most
   * SCOPEs.
   */
  uint8_t d_numIgnoredScopes;
  /** Assumptions corresponding to user-defined functions */
  std::unordered_set<Node> d_defs;
  /** Add LFSC rule to cdp with children, args, conc */
  void addLfscRule(CDProof* cdp,
                   Node conc,
                   const std::vector<Node>& children,
                   LfscRule lr,
                   const std::vector<Node>& args);
  /** Make chained form of a term */
  Node mkChain(Kind k, const std::vector<Node>& children);
  /** 
   * Reconstruct the proof for congruence proving res with the given
   * children, populate into cdp. Used for:
   * (1) CONG over operator startOp != null,
   * (2) HO_CONG, where startOp = null.
   */
  void updateCong(Node res,
                  const std::vector<Node>& children,
                  CDProof* cdp,
                  Node startOp);
  /** Make fresh dummy predicate */
  static Node mkDummyPredicate();
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the Lfsc calculus.
 */
class LfscProofPostprocess : protected EnvObj
{
 public:
  LfscProofPostprocess(Env& env, LfscNodeConverter& ltp);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  std::unique_ptr<LfscProofPostprocessCallback> d_cb;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
