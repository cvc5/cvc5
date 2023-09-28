/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The post processor for the experimental Alf format.
 */

#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF_POST_PROCESSOR_H
#define CVC4__PROOF__ALF_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "proof/alf/alf_node_converter.h"
#include "proof/alf/alf_proof_rule.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_updater.h"

namespace cvc5::internal {

namespace proof {

/**
 * A callback class used by the Alf convereter for post-processing proof
 * nodes by replacing internal rules by the rules in the Alf calculus.
 */
class AlfProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  AlfProofPostprocessCallback(ProofNodeManager* pnm, AlfNodeConverter& atp);
  /**
   * Initialize, called once for each new ProofNode to process. This
   * initializes static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Should update */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;

  /** Update the proof rule application. */
  bool update(Node res,
              ProofRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** Reference to the node converter */
  AlfNodeConverter& d_tproc;
  /**
   * Are we in the first 2 calls to update? This is to distinguish the top-most
   * SCOPEs.
   */
  uint8_t d_numIgnoredScopes;
  /** Optimization to only do unique refl */
  std::map<Node, std::shared_ptr<ProofNode> > d_refl;
  /**
   * Add a ALF step to the proof cdp with given conclusion, children and args.
   */
  bool addAlfStep(AlfRule rule,
                  Node conclusion,
                  const std::vector<Node>& children,
                  const std::vector<Node>& args,
                  CDProof& cdp);
  /** Add a refl step to the proof for n */
  void addReflStep(const Node& n, CDProof& cdp);
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the Alf calculus.
 */
class AlfProofPostprocess : protected EnvObj
{
 public:
  AlfProofPostprocess(Env& env, AlfNodeConverter& atp);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  std::unique_ptr<AlfProofPostprocessCallback> d_cb;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
