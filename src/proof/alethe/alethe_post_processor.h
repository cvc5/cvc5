/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into Alethe proof nodes
 */

#ifndef CVC5__PROOF__ALETHE__ALETHE_PROOF_PROCESSOR_H
#define CVC5__PROOF__ALETHE__ALETHE_PROOF_PROCESSOR_H

#include "proof/alethe/alethe_node_converter.h"
#include "proof/alethe/alethe_proof_rule.h"
#include "proof/proof_node_updater.h"

namespace cvc5::internal {

namespace proof {

/**
 * A callback class used by the Alethe converter for post-processing proof nodes
 * by replacing internal rules by the rules in the Alethe calculus.
 */
class AletheProofPostprocessCallback : protected EnvObj,
                                       public ProofNodeUpdaterCallback
{
 public:
  /** The callback for post-processing proof nodes into the Alethe format.
   *
   * @param env The environment
   * @param anc The Alethe node converter
   * @param resPivots Whether pivots should be used in resolution
   * @param reasonForConversionFailure The reason to be set for conversion
   * failure, if any
   */
  AletheProofPostprocessCallback(Env& env,
                                 AletheNodeConverter& anc,
                                 bool resPivots,
                                 std::string* reasonForConversionFailure);

  ~AletheProofPostprocessCallback() {}

  /** Should proof pn be updated? Only if its top-level proof rule is not an
   *  Alethe proof rule and d_reasonForConversionFailure is not set.
   */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /**
   * This method updates the proof rule application depending on the given
   * rule and translating it into a proof node in terms of the Alethe rules.
   */
  bool update(Node res,
              ProofRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;
  /** Should proof pn be updated at post-visit?
   *
   * Only if its top-level Alethe proof rule is RESOLUTION_OR, REORDERING, or
   * CONTRACTION, which may require updates depending on how the children have
   * changed. And as long as d_reasonForConversionFailure is not set.
   */
  bool shouldUpdatePost(std::shared_ptr<ProofNode> pn,
                        const std::vector<Node>& fa) override;
  /**
   * This method is used to add an additional application of the or-rule between
   * a conclusion (cl (or F1 ... Fn)) and a rule that uses this conclusion as a
   * premise and treats it as a clause, i.e. assumes that it has been printed
   * as (cl F1 ... Fn).
   */
  bool updatePost(Node res,
                  ProofRule id,
                  const std::vector<Node>& children,
                  const std::vector<Node>& args,
                  CDProof* cdp) override;

  /** Ensure the final step of the proof concludes "(cl)".
   *
   * Also sanitizes the arguments of the outer scopes of the proof node.
   */
  bool ensureFinalStep(Node res,
                       ProofRule id,
                       std::vector<Node>& children,
                       const std::vector<Node>& args,
                       CDProof* cdp);

 private:
  /** The Alethe node converter */
  AletheNodeConverter& d_anc;
  /** Whether to keep the pivots in the arguments of the resolution rule. */
  bool d_resPivots;
  /** The cl operator. */
  Node d_cl;
  /** Adds an Alethe step to the CDProof argument
   *
   * The added step to `cdp` uses ProofRule::ALETHE_RULE with `rule` as the
   * first argument, the original conclusion `res` as the second and
   * `conclusion`, the result to be printed (which may or may not differ from
   * `res`), as the third.
   *
   * @param rule The id of the Alethe rule
   * @param res The original conclusion
   * @param conclusion The conclusion to be printed for the step
   * @param children The children of the application
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
   * As above, but `res` must be a node of the form `(or F1 ... Fn)` and the
   * conclusion to be printed will be the clause `(cl F1 ... Fn)`.
   *
   * @param rule The id of the Alethe rule,
   * @param res The original conclusion
   * @param children The children of the application
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return True if the step could be added, or false if not.
   */
  bool addAletheStepFromOr(AletheRule rule,
                           Node res,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           CDProof& cdp);

  /** Test whether the given resolution premise is being used as a singleton
   * clause but is justified as a non-singleton clause, and fix if needed.
   *
   * This happens with `premise` is a node (or F1 ... Fn) whose proof in `cdp`
   * justifies `(cl (or F1 ... Fn))`, but should justify `(cl F1 ... Fn)`. If
   * that is the case, steps will be added to `cdp` to justify the needed
   * clause.
   */
  bool maybeReplacePremiseProof(Node premise, CDProof* cdp);

  /** Nodes corresponding to the Boolean values. */
  Node d_true;
  Node d_false;

  /** The reason for conversion failure, if any. */
  std::string* d_reasonForConversionFailure;
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the Alethe calculus.
 */
class AletheProofPostprocess : protected EnvObj
{
 public:
  AletheProofPostprocess(Env& env, AletheNodeConverter& anc);
  ~AletheProofPostprocess();
  /** Convert the proof node into the Alethe proof format
   *
   * If the conversion is possible, true is returned. Otherwise, false. The
   * conversion may fail if the proof contains unsupported elements in the
   * Alethe proof calculus, such as uncategorized Skolems.
   *
   * The argument reasonForConversionFailure will be set with the reason for
   * failure, if any.
   */
  bool process(std::shared_ptr<ProofNode> pf,
               std::string& reasonForConversionFailure);

 private:
  /** The post process callback */
  AletheProofPostprocessCallback d_cb;

  /** The reason for conversion failure, if any. */
  std::string d_reasonForConversionFailure;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
