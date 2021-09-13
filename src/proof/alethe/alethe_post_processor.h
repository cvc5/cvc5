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
 * The module for processing proof nodes into Alethe proof nodes
 */

#ifndef CVC4__PROOF__ALETHE_PROOF_PROCESSOR_H
#define CVC4__PROOF__ALETHE_PROOF_PROCESSOR_H

#include "proof/proof_node_updater.h"
#include "proof/alethe/alethe_proof_rule.h"

namespace cvc5 {

namespace proof {

/**
 * A callback class used by the Alethe converter for post-processing proof nodes
 * by replacing internal rules by the rules in the Alethe calculus.
 */
class AletheProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  AletheProofPostprocessCallback(ProofNodeManager* pnm);
  ~AletheProofPostprocessCallback() {}
  /** Should proof pn be updated? Only if its top-level proof rule is not an
   *  Alethe proof rule.
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
   * rule and translating it into a proof node in terms of the Alethe rules.
   *
   * @param res The expected result of the application,
   * @param rule The id of the Alethe rule,
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
   * This method adds a new step to the proof applying the ALETHE_RULE. It adds
   * the id of the ALETHE_RULE as the first argument, the res node as the second
   * and third argument.
   *
   * @param res The expected result of the application,
   * @param rule The id of the Alethe rule,
   * @param children The children of the application,
   * @param args The arguments of the application,
   * @param cdp The proof to add to,
   * @return True if the step could be added, or false if not.
   */
  bool addAletheStep(Node res,
                    AletheRule rule,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    CDProof& cdp);
  /**
   * This method adds a new step to the proof applying the ALETHE_RULE but adds
   * a conclusion different from the result as the third argument.
   *
   * @param res The expected result of the application,
   * @param rule The id of the Alethe rule,
   * @param conclusion The conclusion of the application as the Alethe printer
   * @param children The children of the application,
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return True if the step could be added, or false if not.
   */
  bool addAletheStep(Node res,
                    AletheRule rule,
                    Node conclusion,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    CDProof& cdp);
  /**
   * This method adds a new step to the proof applying the Alethe rule while
   * replacing the outermost or by cl, i.e. (cl F1 ... Fn). The kind of the
   * given Node has to be OR.
   *
   * @param res The expected result of the application in form (or F1 ... Fn),
   * @param rule The id of the Alethe rule,
   * @param children The children of the application,
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return True if the step could be added, or false if not.
   */
  bool addAletheStepFromOr(Node res,
                          AletheRule rule,
                          const std::vector<Node>& children,
                          const std::vector<Node>& args,
                          CDProof& cdp);
};

}  // namespace proof

}  // namespace cvc5

#endif
