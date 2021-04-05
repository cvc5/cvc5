/*********************                                                        */
/*! \file verit_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into veriT proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__VERIT_PROOF_PROCESSOR_H
#define CVC4__PROOF__VERIT_PROOF_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_node_updater.h"
#include "proof/verit/verit_proof_rule.h"

namespace cvc5 {

namespace proof {

/**
 * A callback class used by the veriT converter for post-processing proof nodes
 * by replacing internal rules by the rules in the veriT calculus.
 */
class VeritProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  VeritProofPostprocessCallback(ProofNodeManager* pnm);
  ~VeritProofPostprocessCallback() {}
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /**
   * This method updates the proof rule application by splitting on the given
   * rule and translating it into a proof node in terms of the veriT rules.
   *
   * @param res The expected result of the application,
   * @param rule The id of the veriT rule,
   * @param children The children of the application,
   * @param args The arguments of the application,
   * @param cdp The proof to add to,
   * @return True if the step could be added, or null if not.
   */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  NodeManager* d_nm;
  /**
   * This method adds a new step to the proof applying the veriT rule.
   *
   * @param res The expected result of the application,
   * @param rule The id of the veriT rule,
   * @param children The children of the application,
   * @param args The arguments of the application,
   * @param cdp The proof to add to,
   * @return True if the step could be added, or null if not.
   */
  bool addVeritStep(Node res,
                    VeritRule rule,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    CDProof& cdp);
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the veriT calculus.
 */
class VeritProofPostprocess
{
 public:
  VeritProofPostprocess(ProofNodeManager* pnm);
  ~VeritProofPostprocess();
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The post process callback */
  std::unique_ptr<ProofNodeUpdaterCallback> d_cb;

  // TODO: infrastructure from ProofNodeUpdater
  void processInternal(std::shared_ptr<ProofNode> pf,
                       const std::vector<Node>& fa);
  bool runUpdate(std::shared_ptr<ProofNode> cur,
                 const std::vector<Node>& fa,
                 bool& continueUpdate);

  bool d_debugFreeAssumps;
  std::vector<Node> d_freeAssumps;
};

}  // namespace proof

}  // namespace cvc5

#endif
