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

#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof_node_updater.h"

namespace cvc5 {

namespace proof {

/**
 * A callback class used by the Alethe converter for post-processing proof nodes
 * by replacing internal rules by the rules in the Alethe calculus.
 */
class AletheProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  AletheProofPostprocessCallback(ProofNodeManager* pnm,
                                 AletheNodeConverter& anc);
  ~AletheProofPostprocessCallback() {}
  /** Should proof pn be updated? Only if its top-level proof rule is not an
   *  Alethe proof rule.
   */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /**
   * This method updates the proof rule application depending on the given
   * rule and translating it into a proof node in terms of the Alethe rules.
   */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;
  /**
   * This method is used to add an additional application of the or-rule between
   * a conclusion (cl (or F1 ... Fn)) and a rule that uses this conclusion as a
   * premise and treats it as a clause, i.e. assumes that it has been printed
   * as (cl F1 ... Fn).
   */
  bool finalize(Node res,
                PfRule id,
                const std::vector<Node>& children,
                const std::vector<Node>& args,
                CDProof* cdp);
  /**
   * This method is used to add some last steps to a proof when this is
   * necessary. The final step should always be printed as (cl). However:
   *
   * 1. If the last step of a proof is reached (which is false) it is printed as
   * (cl false).
   * 2. If one of the assumptions is false it is printed as false.
   *
   * Thus, an additional resolution step with (cl (not true)) has to be added to
   * transform (cl false) or false into (cl).
   *
   */
  bool finalStep(Node res,
                 PfRule id,
                 const std::vector<Node>& children,
                 const std::vector<Node>& args,
                 CDProof* cdp);

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The Alethe node converter */
  AletheNodeConverter& d_anc;
  /** The cl operator
   * For every step the conclusion is a clause. But since the or operator
   *requires at least two arguments it is extended by the cl operator. In case
   *of more than one argument it corresponds to or otherwise it is the identity.
   **/
  Node d_cl;
  /**
   * This method adds a new ALETHE_RULE step to the proof, with `rule` as the
   * first argument, the original conclusion `res` as the second and
   * `conclusion`, the result to be printed (which may or may not differ from
   * `res`), as the third.
   *
   * @param rule The id of the Alethe rule,
   * @param res The expected result of the application,
   * @param conclusion The conclusion to be printed for the step
   * @param children The children of the application,
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return True if the step could be added, or false if not.
   */
  bool addAletheStep(AletheRule rule,
                     Node res,
                     Node conclusion,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args,
                     CDProof& cdp);
  /**
   * As above, but for proof nodes with original conclusions of the form `(or F1
   * ... Fn)` whose conclusion-to-be-printed must be `(cl F1 ... Fn)`.
   *
   * This method internally calls addAletheStep. The kind of the given Node has
   * to be OR.
   *
   * @param rule The id of the Alethe rule,
   * @param res The expected result of the application in form (or F1 ... Fn),
   * @param children The children of the application,
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return True if the step could be added, or false if not.
   */
  bool addAletheStepFromOr(AletheRule rule,
                           Node res,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           CDProof& cdp);
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the Alethe calculus.
 */
class AletheProofPostprocess
{
 public:
  AletheProofPostprocess(ProofNodeManager* pnm, AletheNodeConverter& anc);
  ~AletheProofPostprocess();
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The post process callback */
  AletheProofPostprocessCallback d_cb;
};

}  // namespace proof

}  // namespace cvc5

#endif
