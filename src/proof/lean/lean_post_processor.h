/*********************                                                        */
/*! \file lean_post_proccessor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for proccessing proof nodes into Lean proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LEAN_POST_PROCESSOR_H
#define CVC4__PROOF__LEAN_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_node_updater.h"
#include "proof/lean/lean_rules.h"

namespace CVC4 {

namespace proof {

/**
 * A callback class used by the Lean convereter for post-proccessing proof nodes
 * by replacing internal rules by the rules in the Lean calculus.
 */
class LeanProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  LeanProofPostprocessCallback(ProofNodeManager* pnm);
  /**
   * Initialize, called once for each new ProofNode to proccess. This
   * initializes static information to be used by successive calls to update.
   */
  void initializeUpdate();
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
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
  NodeManager* d_nm;
  ProofChecker* d_pc;
  bool addLeanStep(Node res,
                   LeanRule rule,
                   const std::vector<Node>& children,
                   const std::vector<Node>& args,
                   CDProof& cdp);
};

/**
 * The proof postproccessor module. This postproccesses a proof node into one
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
}  // namespace CVC4

#endif
