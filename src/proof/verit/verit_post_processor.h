/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into veriT proof nodes
 */

#ifndef CVC4__PROOF__VERIT_PROOF_PROCESSOR_H
#define CVC4__PROOF__VERIT_PROOF_PROCESSOR_H

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
  /** Should proof pn be updated?
   *
   * @param pn the proof node that maybe should be updated
   * @param continueUpdate indicates whether we should continue recursively
   * updating pn
   * @return whether we should run the update method on pn
   */
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
  /** The node manager */
  NodeManager* d_nm;
  /** The variable cl **/
  Node d_cl;
  /**
   * This method adds a new step to the proof applying the VERIT_RULE. It adds
   * the id of the VERIT_RULE as the first argument, the res node as the second
   * and third argument.
   *
   * @param res The expected result of the application,
   * @param rule The id of the veriT rule,
   * @param children The children of the application,
   * @param args The arguments of the application,
   * @param cdp The proof to add to,
   * @return True if the step could be added, or false if not.
   */
  bool addVeritStep(Node res,
                    VeritRule rule,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    CDProof& cdp);
  /**
   * This method adds a new step to the proof applying the VERIT_RULE but adds
   * a conclusion different from the result as the third argument.
   *
   * @param res The expected result of the application,
   * @param rule The id of the veriT rule,
   * @param conclusion The conclusion of the application as the veriT printer
   * @param children The children of the application,
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return True if the step could be added, or false if not.
   */
  bool addVeritStep(Node res,
                    VeritRule rule,
                    Node conclusion,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    CDProof& cdp);
  /**
   * This method adds a new step to the proof applying the veriT rule while
   * replacing the outermost or by cl, i.e. (cl F1 ... Fn). The kind of the
   * given Node has to be OR.
   *
   * @param res The expected result of the application in form (or F1 ... Fn),
   * @param rule The id of the veriT rule,
   * @param children The children of the application,
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return True if the step could be added, or false if not.
   */
  bool addVeritStepFromOr(Node res,
                          VeritRule rule,
                          const std::vector<Node>& children,
                          const std::vector<Node>& args,
                          CDProof& cdp);
};

/**
 * Final callback class used by the veriT to add last step to proof in certain
 * cases.
 */
class VeritProofPostprocessFinalCallback : public ProofNodeUpdaterCallback
{
 public:
  VeritProofPostprocessFinalCallback(ProofNodeManager* pnm);
  ~VeritProofPostprocessFinalCallback() {}
  /** Should proof pn be updated?
   *
   * @param pn the proof node that maybe should be updated
   * @param continueUpdate indicates whether we should continue recursively
   * updating pn
   * @return whether we should run the update method on pn
   */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /**
   * This method gets a proof node pn = false printed as (cl false) and updates
   * the proof for false such that (cl) is printed.
   *
   * @param res The expected result of the application,
   * @param rule The id of the veriT rule,
   * @param children The children of the application,
   * @param args The arguments of the application,
   * @param cdp The proof to add to,
   * @return True if the step could be added, or false if not.
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
  /** The node manager */
  NodeManager* d_nm;
  /** The variable cl **/
  Node d_cl;
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
  VeritProofPostprocessCallback d_cb;
  /** The updater, which is responsible for translating proof rules */
  ProofNodeUpdater d_updater;
  /** The final post process callback */
  VeritProofPostprocessFinalCallback d_fcb;
  /** The updater, which is responsible for adding additional steps to the end
   * of the proof */
  ProofNodeUpdater d_finalize;
};

}  // namespace proof

}  // namespace cvc5

#endif
