/*********************                                                        */
/*! \file lean_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into Lean proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF__LEAN_POST_PROCESSOR_H
#define CVC4__PROOF__LEAN_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_checker.h"
#include "expr/proof_node_updater.h"
#include "proof/lean/lean_rules.h"

namespace cvc5 {

namespace proof {

/**
 * A callback class used by the Lean convereter for post-processing proof nodes
 * by replacing internal rules by the rules in the Lean calculus.
 */
class LeanProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  LeanProofPostprocessCallback(ProofNodeManager* pnm);
  /**
   * Initialize, called once for each new ProofNode to process. This
   * initializes static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Update the proof node iff has the LEAN_RULE id. */
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
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The proof checker is used to generate conclusions from local
   * proof steps. This is currently only used in the resolution rule.
   */
  ProofChecker* d_pc;

  /**
   * Recall the Lean rule:
   *  Children: (P1 ... Pn)
   *  Arguments: (id, Q, A1, ..., Am)
   *  ---------------------
   *  Conclusion: (Q)
   *  The id argument is a LeanRule, as defined in proof/lean/lean_rules.h
   *  This allows us to specify which rule in the Lean calculus the current rule
   *  corresponds to.
   * addLeanStep encapsulates translation boilerplate by adding id and Q to
   * arguments, and children and args are passed along verbatim.
   */
  bool addLeanStep(Node res,
                   LeanRule rule,
                   const std::vector<Node>& children,
                   const std::vector<Node>& args,
                   CDProof& cdp);
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the Lean calculus.
 */
class LeanProofPostprocess
{
 public:
  LeanProofPostprocess(ProofNodeManager* pnm);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  std::unique_ptr<LeanProofPostprocessCallback> d_cb;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace proof
}  // namespace cvc5

#endif
